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
export CONTROLLED_SCI_MAX=4294967296 CONTROLLED_SCI_CURRENT=1342177280
export CONTROLLED_CLI_MAX=536870912 CONTROLLED_CLI_CURRENT=268435456
export BASH_ENV="$repo/tests/shell/fixtures/resource_admission/bash-env.sh"
printf 'MemAvailable: 16454287 kB\n' > "$scratch/host/meminfo"
printf 'full avg10=4.82 avg60=1.09 avg300=0.23 total=324417078\n' > "$scratch/host/pressure"
run() {
  local expected=$1 mode=$2 phase=$3 status member=${4:-A}
  set +e
  bash "$operations/resource-check.sh" "$scratch/funding" "$member" "$phase" "$mode" > "$scratch/$phase.log" 2>&1
  status=$?
  set -e
  test "$status" = "$expected"
  printf 'PASS %s mode=%s status=%s\n' "$phase" "$mode" "$status"
}
run 0 ongoing original_review
runtime="$scratch/run/A/author-workspace/output/runtime"
rg -q 'avg10=4.82 avg60=1.09 avg300=0.23' "$runtime/resources-original_review.psi"
rg -q 'Pressure warning:' "$runtime/resources-original_review.psi"
rg -q 'incrementalGrowthBound=3221225472 bytes' "$runtime/resources-original_review.operation-budget"
run 77 full growth_rejected
run 77 replacement replacement_rejected
printf 'MemAvailable: 4718592 kB\n' > "$scratch/host/meminfo"
run 76 ongoing insufficient_operation_ram
printf 'MemAvailable: 5767168 kB\n' > "$scratch/host/meminfo"
run 0 ongoing resident_charge_not_reserved_twice
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
export CONTROLLED_SCI_MAX=4294967297
run 1 ongoing wrong_selected_scope_cap
export CONTROLLED_SCI_MAX=4294967296 CONTROLLED_PROCESS_STATE=not-found
run 0 ongoing absent_scope_conservative_bound
rg -q 'not measured residual' "$runtime/resources-absent_scope_conservative_bound.operation-budget"
unset CONTROLLED_PROCESS_STATE
export CONTROLLED_COMMON_CURRENT=8455716864
printf 'MemAvailable: 2232320 kB\n' > "$scratch/host/meminfo"
printf 'full avg10=4.82 avg60=1.09 avg300=0.23 total=324417078\n' > "$scratch/host/pressure"
run 0 ongoing common_residual_clamp
rg -q 'incrementalGrowthBound=134217728 bytes' "$runtime/resources-common_residual_clamp.operation-budget"
export CONTROLLED_COMMON_CURRENT=1610612736
printf 'MemAvailable: 16454287 kB\n' > "$scratch/host/meminfo"

# Same original publication owner: a new headless256Mi/CLI0 member joins A,
# while A's original run budgets and unit namespace remain unchanged.
mkdir "$scratch/admin-run"
jq -n --arg root "$scratch" '{phase:"headless-control",
  predecessor_program_root:($root+"/funding"),run_template_root:($root+"/run"),
  resource_policy:{per_author_science_mib:256,per_author_cli_mib:0},members:[],retired_members:[],
  additional_authors:[{slot:"ADMIN",run_owner_root:($root+"/admin-run"),display:0,cpu:0,
    input_root:"/controlled/not-science",native_port:0,native_ack_port:0,viewer_port:0,
    viewer_ack_port:0,vnc_port:0,helper_custody:{program_root:($root+"/admin-run"),slot:"ADMIN"}}]
}' > "$scratch/admin-run/successor-declaration.json"
printf '{"target":"/controlled/no-install","source_head":"controlled"}\n' > "$scratch/qualification.json"
bash "$operations/project-program.sh" prepare "$scratch/funding" "$scratch/admin-run" "$scratch/qualification.json"
printf 'Controlled admin publication only; no SCI launch.\n' > "$scratch/admin-run/PARENT-RELEASE.rst"
(cd "$scratch/admin-run"; sha256sum program.json successor-declaration.json PARENT-RELEASE.rst > READY-FREEZE.sha256)
FLEET_PARENT_RELEASED=1 bash "$operations/project-program.sh" publish "$scratch/funding" "$scratch/admin-run" \
  "$(sha256sum "$scratch/funding/program.json" | cut -d' ' -f1)"
run 0 ongoing continuing_original_scope_owner
rg -q 'bounded-control-a-mcp.scope.*cap=4294967296' "$runtime/resources-continuing_original_scope_owner.operation-budget"
export CONTROLLED_SCI_MAX=268435456 CONTROLLED_SCI_CURRENT=134217728
export CONTROLLED_CLI_MAX=0 CONTROLLED_CLI_CURRENT=0
printf 'MemAvailable: 2232320 kB\n' > "$scratch/host/meminfo"
run 0 ongoing headless_disabled_cli ADMIN
admin_runtime="$scratch/admin-run/ADMIN/author-workspace/output/runtime"
rg -q 'incrementalGrowthBound=134217728 bytes' "$admin_runtime/resources-headless_disabled_cli.operation-budget"
export CONTROLLED_SCI_MAX=4294967296 CONTROLLED_SCI_CURRENT=1342177280
export CONTROLLED_CLI_MAX=536870912 CONTROLLED_CLI_CURRENT=268435456
printf 'MemAvailable: 16454287 kB\n' > "$scratch/host/meminfo"
sha256sum "$runtime/resources-original_review".* > "$scratch/original-receipt.sha256"
run 1 ongoing original_review
sha256sum --check --quiet "$scratch/original-receipt.sha256"
printf '1\n' > "$runtime/first-mcp-started.epoch"
run 1 ongoing expired_clock
(cd "$scratch/run"; sha256sum --check --quiet READY-FREEZE.sha256)
test ! -e "$runtime/mcp.stdin"
printf 'PASS original immutable run, deadline, receipt uniqueness and no client/native custody preserved\n'
