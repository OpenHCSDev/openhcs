#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "${1:?root}" "${2:?slot}"
config=$(jq -er '.author_config' "$FLEET_RUN_ROOT/program.json")
cli=$(jq -er '.cli' "$FLEET_RUN_ROOT/program.json")
skill="$FLEET_INSTALL/openhcs/agent/resources/knowledge/packaging/codex/openhcs/skills/use-openhcs"
if [[ "${3:-}" == --preflight ]]; then
  printf 'root=%s slot=%s cwd=%s config=%s skill=%s cli=%s unit=%s fresh=exec\n' "$FLEET_ROOT" "$FLEET_SLOT" "$FLEET_WORKSPACE" "$config" "$skill" "$cli" "$FLEET_UNIT-author"
  printf 'model=%s provider=%s effort=%s cpu=%s display=%s native=%s viewer=%s session-bind=%s\n' "$(jq -er '.model' "$FLEET_RUN_ROOT/program.json")" "$(jq -er '.model_provider' "$FLEET_RUN_ROOT/program.json")" "$(jq -er '.reasoning_effort' "$FLEET_RUN_ROOT/program.json")" "$FLEET_CPU" "$FLEET_DISPLAY" "$FLEET_NATIVE" "$FLEET_VIEWER" "$FLEET_WORKSPACE/output/native-sessions"
  printf 'input=%s read=%s:%s:%s write=%s workers=%s\n' "$FLEET_INPUT" "$FLEET_INPUT" "$FLEET_WORKSPACE/output" "$FLEET_INSTALL/openhcs/agent/resources/knowledge" "$FLEET_WORKSPACE/output" "$(jq -er '.proposed_resource_envelope.science_workers_per_author' "$FLEET_RUN_ROOT/program.json")"
  exit
fi
test "$FLEET_PARENT_RELEASED" = 1
fleet_require_writer_release
test -f "$FLEET_RUN_ROOT/PARENT-RELEASE.rst"
test -f "$FLEET_RUN_ROOT/READY-FREEZE.sha256"
(cd "$FLEET_RUN_ROOT"; sha256sum --check --quiet READY-FREEZE.sha256)
mkdir -p "$FLEET_WORKSPACE/output/runtime" "$FLEET_WORKSPACE/output/native-sessions"
runtime="$FLEET_WORKSPACE/output/runtime"
if [[ "${3:-}" != --inside-scope ]]; then
  systemctl --user is-active --quiet "$FLEET_SLICE"
  test "$(systemctl --user show "$FLEET_SLICE" -p MemoryMax --value)" = "$((FLEET_COMBINED_MIB*1048576))"
  test "$(systemctl --user show "$FLEET_SLICE" -p MemorySwapMax --value)" = 0
  bash "$FLEET_OPERATIONS/resource-check.sh" "$FLEET_ROOT" "$FLEET_SLOT" author_launch ongoing
  cap=$(jq -er '.proposed_resource_envelope.per_author_cli_mib' "$FLEET_RUN_ROOT/program.json")
  cpu=$(jq -er '.proposed_resource_envelope.cpu_quota_per_author_percent' "$FLEET_RUN_ROOT/program.json")
  exec /usr/bin/systemd-run --user --scope --slice="$FLEET_SLICE" --unit="$FLEET_UNIT-author" -p MemoryMax="${cap}M" -p MemorySwapMax=0 -p CPUQuota="${cpu}%" /usr/bin/taskset -c "$FLEET_CPU" /bin/bash "$FLEET_OPERATIONS/launch-author.sh" "$FLEET_ROOT" "$FLEET_SLOT" --inside-scope
fi
test ! -e "$runtime/author-events.typescript"
test ! -e "$runtime/author-events.timing"
cd "$FLEET_WORKSPACE"
printf -v command '%q ' bwrap --bind / / --proc /proc --dev-bind /dev /dev --ro-bind "$FLEET_INPUT" "$FLEET_INPUT" --bind "$FLEET_WORKSPACE/output/native-sessions" /home/ts/.codex/sessions --tmpfs /home/ts/.codex/archived_sessions --tmpfs /home/ts/.codex/skills --tmpfs /home/ts/.codex/memories --ro-bind /dev/null /home/ts/.agent-comms/.pi/APPEND_SYSTEM.md --ro-bind "$config" /home/ts/.codex/config.toml --ro-bind "$skill" /home/ts/.codex/skills/use-openhcs --chdir "$FLEET_WORKSPACE" "$cli" exec --json --skip-git-repo-check --color never -o output/FINAL.rst "Read TASK.rst in the current workspace. Complete the released public analysis autonomously within its recorded resource, evidence and time bounds; freeze and report the final attempted pipeline even on rejection or abstention."
exec /usr/bin/flock --nonblock -E 75 "$FLEET_RUN_ROOT/$FLEET_SLOT/author.lock" /usr/bin/script --quiet --flush --return --log-out "$runtime/author-events.typescript" --log-timing "$runtime/author-events.timing" --command "$command"
