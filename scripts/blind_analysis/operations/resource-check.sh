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
# Growth qualification is not a universal stop for a bounded continuation.
# The same owner requires actual host headroom below; PSI is
# telemetry for ongoing work, and fatal when admitting future fleet growth.
case "$mode" in
  ongoing) pressure_policy=warning ;;
  full|replacement|bootstrap) pressure_policy=reject ;;
  ledger) pressure_policy=ledger ;;
  *) exit 64 ;;
esac
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
remaining=0
for ((i=old_count;i<${#outputs[@]};i++)); do
  limits=$(fleet_limits_for "${authors[i-old_count]}")
  scratch_estimate=$(jq -er '.scratch_per_author_mib*1048576' <<< "$limits")
  output_estimate=$(jq -er '.output_per_author_mib*1048576' <<< "$limits")
  reserved=$((reserved+output_estimate+scratch_estimate))
  output=${outputs[i]}
  bytes=0; scratch=0
  if [[ -d "$output" ]]; then bytes=$(du -s -B1 "$output" | cut -f1); fi
  if [[ -d "$output/runtime/scratch" ]]; then scratch=$(du -s -B1 "$output/runtime/scratch" | cut -f1); fi
  printf 'Current %s total=%s scratch=%s retained=%s growthEstimates=%s/%s\n' "$output" "$bytes" "$scratch" "$((bytes-scratch))" "$output_estimate" "$scratch_estimate" | tee -a "$receipt.output"
  # Original programme values plan remaining physical HOME growth; they are
  # not output/scratch quotas. Actual usage beyond an estimate is measured,
  # never a selected-author or sibling veto. No negative growth is credited.
  retained_growth=$((output_estimate-bytes+scratch))
  scratch_growth=$((scratch_estimate-scratch))
  if [[ "$retained_growth" -lt 0 ]]; then retained_growth=0; fi
  if [[ "$scratch_growth" -lt 0 ]]; then scratch_growth=0; fi
  remaining=$((remaining+retained_growth+scratch_growth))
  total=$((total+bytes))
done
printf 'Programme old=%s current=%s reservedCurrent=%s\n' "$old" "$total" "$reserved" | tee -a "$receipt.output"
printf 'Operational policy: retained-output/scratch byte quotas removed; programme amounts are growth estimates, not limits. Actual HOME/RAM/pressure and owned cleanup remain authoritative.\n' | tee -a "$receipt.output"
# Historical allocations are observations, already reflected in df free space.
# Only still-funded output/scratch growth is reserved against actual HOME.
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
# The existing slice identifies the physical family, not an invented capacity.
# Charge and swap are observations; never derive host headroom from a hard cap.
current=$(systemctl --user show "$FLEET_SLICE" -p MemoryCurrent --value)
[[ "$current" =~ ^[0-9]+$ ]]
swap=$(systemctl --user show "$FLEET_SLICE" -p MemorySwapCurrent --value)
[[ "$swap" =~ ^[0-9]+$ ]]
printf 'Joint slice %s measuredCharge=%s measuredSwap=%s bytes\n' "$FLEET_SLICE" "$current" "$swap" | tee "$receipt.ram-scopes"
# RSS/PSS come from this exact kernel-owned family, not a copied funded PID list.
cgroup=$(systemctl --user show "$FLEET_SLICE" -p ControlGroup --value)
[[ "$cgroup" == /* && "$cgroup" != / ]]
rss=0; pss=0; observed=0; vanished=0
while IFS= read -r pid; do
  [[ "$pid" =~ ^[0-9]+$ ]] || exit 1
  if sample=$(awk '/^Rss:/ {rss=$2} /^Pss:/ {pss=$2} END {printf "%d %d",rss,pss}' "/proc/$pid/smaps_rollup" 2>/dev/null); then
    read -r process_rss process_pss <<< "$sample"
    rss=$((rss+process_rss)); pss=$((pss+process_pss)); observed=$((observed+1))
  else vanished=$((vanished+1)); fi
done < <(find "/sys/fs/cgroup$cgroup" -name cgroup.procs -exec cat {} + | sort -nu)
printf 'Family snapshot RSS=%sKiB PSS=%sKiB observed=%s unavailable=%s (not an allocation guarantee)\n' "$rss" "$pss" "$observed" "$vanished" | tee -a "$receipt.ram-scopes"
if [[ "$mode" == replacement || "$mode" == bootstrap ]]; then
  if [[ "$mode" == bootstrap ]]; then fleet_require_bootstrap_custody; else fleet_require_helpers; fi
fi
psi_max=$(jq -er '.proposed_resource_envelope.full_memory_psi_max_percent | select(type=="number" and .>=0 and .<=100)' <<< "$FLEET_PROGRAM")
awk -v floor="$floor" '/MemAvailable:/ {printf "MemAvailable %.3f GiB; required %d MiB\n",$2/1048576,floor; if($2<floor*1024) exit 76}' /proc/meminfo | tee "$receipt.ram"
printf 'Pressure admission mode=%s policy=%s limit=%s%%; measured desktop headroom and all windows retained\n' "$mode" "$pressure_policy" "$psi_max" | tee "$receipt.psi-policy"
awk -v limit="$psi_max" -v policy="$pressure_policy" '
  BEGIN {count=split("avg10 avg60 avg300", required, " ")}
  /^full / {
    print
    for(i=2;i<=NF;i++) {
      split($i, field, "=")
      for(j=1;j<=count;j++) if(field[1]==required[j]) {
        if(seen[field[1]]++ || field[2] !~ /^[0-9]+([.][0-9]+)?$/) invalid=1
        else if(field[2]+0>limit) {
          printf "Pressure %s: full %s=%s exceeds declared %s%%\n", policy, field[1], field[2], limit
          exceeded=1
        }
      }
    }
  }
  END {
    for(j=1;j<=count;j++) if(seen[required[j]]!=1) invalid=1
    if(invalid || (exceeded && policy=="reject")) exit 77
  }
' /proc/pressure/memory | tee "$receipt.psi"
printf 'Admission PASS\n'
