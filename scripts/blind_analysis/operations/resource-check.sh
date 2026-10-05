#!/bin/bash
# NEXT revision of the original admission/ledger owner, not a second gate.
set -euo pipefail
# Publication and one complete admission cannot observe half a transition.
exec 9>"${1:?root}/program.lock"
flock --shared 9
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "$1" "${2:?slot}"
phase=${3:?unique observation}
case "$phase" in ''|*[!a-zA-Z0-9_-]*) exit 64;; esac
mode=${4:?explicit operation mode: ongoing, full, replacement, bootstrap or ledger}
# Growth qualification is not a universal stop for a bounded continuation.
# Desktop reserve describes future growth admission. Below-reserve
# ongoing observations must still be able to resolve jobs and release buffers.
case "$mode" in
  ongoing) memory_policy=warning; disk_policy=warning; deadline_policy=warning ;;
  full|replacement|bootstrap) memory_policy=reject; disk_policy=reject; deadline_policy=reject ;;
  ledger) memory_policy=ledger; disk_policy=warning; deadline_policy=warning ;;
  *) exit 64 ;;
esac
runtime="$FLEET_WORKSPACE/output/runtime"
mkdir -p "$runtime"
receipt="$runtime/resources-$phase"
test ! -e "$receipt.output"
test ! -e "$receipt.deadline"
if [[ -e "$runtime/first-mcp-started.epoch" ]]; then
  started=$(<"$runtime/first-mcp-started.epoch")
  minutes=$(jq -cr '.task_minutes_from_first_mcp_start |
    if . == null then null
    elif type=="number" then
      if .>0 and .==floor then . else error("invalid declared scientific interval") end
    else error("invalid declared scientific interval") end' "$FLEET_RUN_ROOT/program.json")
  elapsed=$(($(date -u +%s)-started))
  if [[ "$minutes" == null ]]; then
    printf 'Recorded elapsed=%s seconds; scientific interval undeclared; mode=%s. Preserve checkpoints and continue through measured resource admission.\n' "$elapsed" "$mode" | tee "$receipt.deadline"
  else
    printf 'Deadline elapsed=%s allowed=%s seconds; mode=%s policy=%s\n' "$elapsed" "$((minutes*60))" "$mode" "$deadline_policy" | tee "$receipt.deadline"
    if [[ "$elapsed" -ge "$((minutes*60))" ]]; then
      printf 'Scientific interval expired: no new scientific work or process startup. Existing-client observation, evidence freeze and exact owned cleanup remain permitted; ledger is not dispatch permission.\n' | tee -a "$receipt.deadline"
      [[ "$deadline_policy" != reject ]]
    fi
  fi
fi
# Ongoing means an already recorded live client, not permission to bootstrap
# another process. The existing recorder owns this incarnation and its clock.
if [[ "$mode" == ongoing ]]; then fleet_require_live_client; fi

# Canonicalize custody once and reject overlaps. Closed bytes are already in df;
# the cleanup owner inventories them, not each scientific action.
outputs=()
retained_roots=$(jq -ce '.retained_output_roots | select(type=="array")' <<< "$FLEET_PROGRAM")
while IFS= read -r output; do outputs+=("$(realpath -m "$output")"); done \
  < <(jq -er '.[]' <<< "$retained_roots")
old_count=${#outputs[@]}
funded_slots=$(fleet_funded_slots)
authors=()
while IFS= read -r author; do
  authors+=("$author")
  while IFS= read -r output; do outputs+=("$(realpath -m "$output")"); done \
    < <(fleet_output_roots_for "$author")
done <<< "$funded_slots"
for ((i=0;i<${#outputs[@]};i++)); do
  for ((j=i+1;j<${#outputs[@]};j++)); do
    if [[ "${outputs[i]}" == "${outputs[j]}" || "${outputs[i]}" == "${outputs[j]}/"* || "${outputs[j]}" == "${outputs[i]}/"* ]]; then
      printf 'Overlapping ledger roots: %s / %s\n' "${outputs[i]}" "${outputs[j]}" >&2
      exit 79
    fi
  done
done
total=0
reserved=0
remaining=0
for author in "${authors[@]}"; do
  # An ongoing observation measures its own output, not recursive sibling trees.
  # The existing ledger/startup modes report the complete funded growth forecast.
  if [[ "$mode" == ongoing && "$author" != "$FLEET_SLOT" ]]; then continue; fi
  limits=$(fleet_limits_for "$author")
  scratch_estimate=$(jq -er '.scratch_per_author_mib*1048576' <<< "$limits")
  output_estimate=$(jq -er '.output_per_author_mib*1048576' <<< "$limits")
  reserved=$((reserved+output_estimate+scratch_estimate))
  bytes=0; scratch=0
  while IFS= read -r output; do
    if [[ -d "$output" ]]; then bytes=$((bytes+$(du -s -B1 "$output" | cut -f1))); fi
  done < <(fleet_output_roots_for "$author")
  artifact=$(fleet_artifact_root_for "$author")
  if [[ -d "$artifact/runtime/scratch" ]]; then scratch=$(du -s -B1 "$artifact/runtime/scratch" | cut -f1); fi
  printf 'Current %s payload=%s member=%s total=%s scratch=%s retained=%s growthEstimates=%s/%s\n' "$(fleet_workspace_for "$author")/output" "$artifact" "$author" "$bytes" "$scratch" "$((bytes-scratch))" "$output_estimate" "$scratch_estimate" | tee -a "$receipt.output"
  # Original programme values plan remaining physical destination growth; they are
  # not output/scratch quotas. Actual usage beyond an estimate is measured,
  # never a selected-author or sibling veto. No negative growth is credited.
  retained_growth=$((output_estimate-bytes+scratch))
  scratch_growth=$((scratch_estimate-scratch))
  if [[ "$retained_growth" -lt 0 ]]; then retained_growth=0; fi
  if [[ "$scratch_growth" -lt 0 ]]; then scratch_growth=0; fi
  remaining=$((remaining+retained_growth+scratch_growth))
  total=$((total+bytes))
done
printf 'Programme retainedRoots=%s measuredCurrent=%s growthEstimate=%s remainingGrowthEstimate=%s scope=%s\n' "$old_count" "$total" "$reserved" "$remaining" "$mode" | tee -a "$receipt.output"
printf 'Operational policy: retained-output/scratch byte quotas removed; programme amounts are growth estimates, not limits. Actual HOME/RAM/pressure and owned cleanup remain authoritative.\n' | tee -a "$receipt.output"
printf 'Operation admission revision: existing recorded-client bounded observations/QA use ongoing warning policy; cold startup and large allocations require replacement/bootstrap/full. No tool-name exception, new client, or UNKNOWN replay is authorized by an ongoing PASS.\n' | tee -a "$receipt.output"
# Forecasts guide cleanup/staging, not permission for an unrelated capture.
# Admission protects actual free HOME; no all-fleet estimate is added to its floor.
home_floor=$(jq -er '.proposed_resource_envelope.minimum_home_ongoing_gib*1073741824' <<< "$FLEET_PROGRAM")
df --output=avail -B1 /home/ts | awk -v floor="$home_floor" -v policy="$disk_policy" '
  NR==2 {
    if($1 !~ /^[0-9]+$/ || $1+0<=0) exit 78
    printf "HomeAvailable %.3f GiB; startupReserve %.3f GiB; policy=%s\n",$1/1073741824,floor/1073741824,policy
    if($1<floor) {
      if(policy=="reject") exit 78
      printf "Disk warning: below startup reserve. Existing-client bounded reads/QA only; no cold launch or bulk allocation permission. Check actual destination writes and coordinate owned cleanup.\n"
    }
    observed=1
  }
  END {if(!observed) exit 78}' | tee "$receipt.disk"
fleet_require_artifact_destination "$FLEET_SLOT"
# Observe the actual write filesystem, not HOME by assumption. No second
# capacity policy or quota: the operation must size writes against this space.
df --output=target,avail -B1 "$FLEET_ARTIFACT_ROOT" | awk '
  {print} NR==2 {observed=1; if($NF !~ /^[0-9]+$/ || $NF+0<=0) exit 78}
  END {if(!observed) exit 78}' | tee "$receipt.destination"
printf 'PayloadDestination=%s ScratchDestination=%s; growth estimates span declared destinations, not an extra HOME reservation.\n' "$FLEET_ARTIFACT_ROOT" "$FLEET_SCRATCH" | tee -a "$receipt.destination"
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
awk -v floor="$floor" -v policy="$memory_policy" '
  /^MemAvailable:/ {
    if(seen++ || NF!=3 || $2 !~ /^[0-9]+$/ || $3!="kB") invalid=1
    else {
      printf "MemAvailable %.3f GiB; desktopReserve %d MiB; policy=%s\n",$2/1048576,floor,policy
      if($2<floor*1024) {
        below=1
        printf "Memory %s: below desktop reserve. Resolve existing jobs and release owned buffers with bounded observations/cleanup; no cold launch or bulk allocation permission. Stage real buffers against current availability.\n",policy
      }
    }
  }
  END {
    if(seen!=1 || invalid) {
      print "Invalid MemAvailable observation" > "/dev/stderr"
      exit 76
    }
    if(below && policy=="reject") exit 76
  }
' /proc/meminfo | tee "$receipt.ram"
printf 'Pressure observation mode=%s; no numeric PSI admission cutoff. Assess recent10/60 windows with host availability, family RSS/PSS and actual incremental buffers; reduce workers or defer expansion when real pressure warrants it. Admission PASS is not an allocation guarantee.\n' "$mode" | tee "$receipt.psi-policy"
awk '
  BEGIN {count=split("avg10 avg60 avg300", required, " ")}
  /^full / {
    print
    for(i=2;i<=NF;i++) {
      split($i, field, "=")
      for(j=1;j<=count;j++) if(field[1]==required[j]) {
        if(seen[field[1]]++ || field[2] !~ /^[0-9]+([.][0-9]+)?$/) invalid=1
        else if(field[2]+0>100) invalid=1
      }
    }
  }
  END {
    for(j=1;j<=count;j++) if(seen[required[j]]!=1) invalid=1
    if(invalid) exit 77
  }
' /proc/pressure/memory | tee "$receipt.psi"
printf 'Admission PASS\n'
