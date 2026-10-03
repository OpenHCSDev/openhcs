#!/bin/bash
# Original resource-check/slot/projector entrypoints; controlled host, no runtime.
set -euo pipefail
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.."; pwd)
scratch=${1:?new persistent validation directory}
test ! -e "$scratch"
mkdir -p "$scratch/run/A/author-workspace/output" "$scratch/host"
operations="$repo/scripts/blind_analysis/operations"
jq -n --arg root "$scratch" --arg operations "$operations" '{
  phase:"bounded-control",funding_root:($root+"/funding"),scope_slice:"controlled.slice",
  source_install:"/controlled/not-imported",python:"/controlled/not-run",operation_owner_root:$operations,
  task_minutes_from_first_mcp_start:75,retained_output_roots:[],
  authors:[{slot:"A",run_owner_root:($root+"/run"),display:94,cpu:0,input_root:"/controlled/input",
    native_port:6012,native_ack_port:7012,viewer_port:6013,viewer_ack_port:7013,vnc_port:5998,
    helper_custody:{program_root:($root+"/run"),slot:"A"}}],
  funded_members:[{slot:"A",run_owner_root:($root+"/run")}],
  proposed_resource_envelope:{aggregate_memory_max_bytes:8589934592,
    total_output_and_scratch_mib:10240,minimum_home_ongoing_gib:2,
    output_per_author_mib:1,scratch_per_author_mib:1,per_author_science_mib:4096,
    per_author_cli_mib:512,helper_caps_mib:{},desktop_growth_reserve_mib:2048,full_memory_psi_max_percent:1}
}' > "$scratch/run/program.json"
printf 'Controlled initialization only; no scientific release.\n' > "$scratch/run/PARENT-RELEASE.rst"
(cd "$scratch/run"; sha256sum program.json PARENT-RELEASE.rst > READY-FREEZE.sha256)
FLEET_PARENT_RELEASED=1 bash "$operations/project-program.sh" initialize "$scratch/funding" "$scratch/run" absent
export CONTROLLED_HOST="$scratch/host" CONTROLLED_HOME_BYTES=8353711390
export CONTROLLED_COMMON_MAX=8589934592 CONTROLLED_COMMON_CURRENT=1610612736 CONTROLLED_COMMON_SWAP=0
export BASH_ENV="$repo/tests/shell/fixtures/resource_admission/bash-env.sh"
printf 'MemAvailable: 16454287 kB\n' > "$scratch/host/meminfo"
printf 'full avg10=4.82 avg60=1.09 avg300=0.23 total=324417078\n' > "$scratch/host/pressure"
run() {
  local expected=$1 mode=$2 phase=$3 status
  set +e
  bash "$operations/resource-check.sh" "$scratch/funding" A "$phase" "$mode" > "$scratch/$phase.log" 2>&1
  status=$?
  set -e
  test "$status" = "$expected"
  printf 'PASS %s mode=%s status=%s\n' "$phase" "$mode" "$status"
}
run 0 ongoing original_review
runtime="$scratch/run/A/author-workspace/output/runtime"
rg -q 'avg10=4.82 avg60=1.09 avg300=0.23' "$runtime/resources-original_review.psi"
rg -q 'Pressure warning:' "$runtime/resources-original_review.psi"
rg -q 'declared=4608 MiB' "$runtime/resources-original_review.operation-budget"
run 77 full growth_rejected
run 77 replacement replacement_rejected
printf 'MemAvailable: 6291456 kB\n' > "$scratch/host/meminfo"
run 76 ongoing insufficient_operation_ram
printf 'MemAvailable: 16454287 kB\n' > "$scratch/host/meminfo"
export CONTROLLED_HOME_BYTES=2147483648
run 78 ongoing insufficient_ledger_disk
export CONTROLLED_HOME_BYTES=8353711390 CONTROLLED_COMMON_SWAP=1
run 1 ongoing unsafe_swap
export CONTROLLED_COMMON_SWAP=0 CONTROLLED_COMMON_CURRENT=8589934593
run 1 ongoing overcharged_slice
export CONTROLLED_COMMON_CURRENT=1610612736
printf 'full avg10=4.82 avg60=invalid avg300=0.23 total=324417078\n' > "$scratch/host/pressure"
run 77 ongoing malformed_telemetry
printf 'full avg10=4.82 avg60=1.09 total=324417078\n' > "$scratch/host/pressure"
run 77 ongoing missing_telemetry
printf 'full avg10=0.00 avg60=0.00 avg300=0.00 total=324417078\n' > "$scratch/host/pressure"
run 0 full low_pressure_growth
run 0 replacement low_pressure_replacement
sha256sum "$runtime/resources-original_review".* > "$scratch/original-receipt.sha256"
run 1 ongoing original_review
sha256sum --check --quiet "$scratch/original-receipt.sha256"
printf '1\n' > "$runtime/first-mcp-started.epoch"
run 1 ongoing expired_clock
(cd "$scratch/run"; sha256sum --check --quiet READY-FREEZE.sha256)
test ! -e "$runtime/mcp.stdin"
printf 'PASS original immutable run, deadline, receipt uniqueness and no client/native custody preserved\n'
