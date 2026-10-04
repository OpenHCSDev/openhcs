#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "${1:?root}" "${2:?slot}"
config=$(jq -er '.author_config' "$FLEET_RUN_ROOT/program.json")
cli=$(jq -er '.cli' "$FLEET_RUN_ROOT/program.json")
skill="$FLEET_INSTALL/openhcs/agent/resources/knowledge/packaging/codex/openhcs/skills/use-openhcs"
# Native context is declared once on the immutable member. A retained child
# must already exist in this run's isolated native session namespace.
history_projection_json=$(jq -ce --arg slot "$FLEET_SLOT" '
  [.authors[] | select(.slot==$slot)] |
  if length!=1 then error("ambiguous author context") else .[0] end |
  if .fresh_history==true and .native_thread_id==null then {argv:[],roots:[]}
  elif .fresh_history==false and (.native_thread_id|type)=="string"
       and (.native_thread_id|length)>0 then
    {argv:["resume",.native_thread_id],roots:[.writer_handoff[] |
      .program_root+"/"+.slot+"/author-workspace/output/native-sessions"]}
  else error("inconsistent author context declaration") end
' "$FLEET_RUN_ROOT/program.json")
mapfile -t history_argv < <(jq -r '.argv[]' <<< "$history_projection_json")
history_mount_argv=()
# Paginated native children retain ancestor rollouts at the canonical sessions
# path. Their immutable writer owners supply the files; Codex owns decoding.
while IFS= read -r ancestor_root; do
  test -d "$ancestor_root"
  while IFS= read -r -d '' ancestor; do
    history_mount_argv+=(--ro-bind "$ancestor" "$ancestor")
    history_mount_argv+=(--ro-bind "$ancestor" "/home/ts/.codex/sessions/${ancestor#"$ancestor_root"/}")
  done < <(find "$ancestor_root" -type f -name 'rollout-*.jsonl' -size +0c -print0)
done < <(jq -r '.roots[]' <<< "$history_projection_json")
if [[ "${3:-}" == --preflight ]]; then
  printf 'root=%s slot=%s cwd=%s config=%s skill=%s cli=%s unit=%s history_args=%s\n' "$FLEET_ROOT" "$FLEET_SLOT" "$FLEET_WORKSPACE" "$config" "$skill" "$cli" "$FLEET_UNIT-author" "$(jq -c '.argv' <<< "$history_projection_json")"
  printf 'model=%s provider=%s effort=%s cpu=%s display=%s native=%s viewer=%s session-bind=%s\n' "$(jq -er '.model' "$FLEET_RUN_ROOT/program.json")" "$(jq -er '.model_provider' "$FLEET_RUN_ROOT/program.json")" "$(jq -er '.reasoning_effort' "$FLEET_RUN_ROOT/program.json")" "$FLEET_CPU" "$FLEET_DISPLAY" "$FLEET_NATIVE" "$FLEET_VIEWER" "$FLEET_WORKSPACE/output/native-sessions"
  printf 'readonly_history_args='; printf '%q ' "${history_mount_argv[@]}"; printf '\n'
  printf 'input=%s read=%s:%s:%s write=%s workers=%s\n' "$FLEET_INPUT" "$FLEET_INPUT" "$FLEET_WORKSPACE/output" "$FLEET_INSTALL/openhcs/agent/resources/knowledge" "$FLEET_WORKSPACE/output" "$(jq -er '.proposed_resource_envelope.science_workers_per_author' "$FLEET_RUN_ROOT/program.json")"
  exit
fi
fleet_require_writer_release
test -f "$FLEET_RUN_ROOT/READY-FREEZE.sha256"
(cd "$FLEET_RUN_ROOT"; sha256sum --check --quiet READY-FREEZE.sha256)
mkdir -p "$FLEET_WORKSPACE/output/runtime" "$FLEET_WORKSPACE/output/native-sessions"
runtime="$FLEET_WORKSPACE/output/runtime"
if [[ "${3:-}" != --inside-scope ]]; then
  systemctl --user is-active --quiet "$FLEET_SLICE"
  test "$(systemctl --user show "$FLEET_SLICE" -p MemoryMax --value)" = "$((FLEET_COMBINED_MIB*1048576))"
  test "$(systemctl --user show "$FLEET_SLICE" -p MemorySwapMax --value)" = 0
  bash "$FLEET_OPERATIONS/resource-check.sh" "$FLEET_ROOT" "$FLEET_SLOT" author_launch ongoing
  cap=$(fleet_process_limit_mib author)
  test "$cap" -gt 0
  cpu=$(jq -er '.proposed_resource_envelope.cpu_quota_per_author_percent' "$FLEET_RUN_ROOT/program.json")
  exec /usr/bin/systemd-run --user --scope --slice="$FLEET_SLICE" --unit="$FLEET_UNIT-author" -p MemoryMax="${cap}M" -p MemorySwapMax=0 -p CPUQuota="${cpu}%" /usr/bin/taskset -c "$FLEET_CPU" /bin/bash "$FLEET_OPERATIONS/launch-author.sh" "$FLEET_ROOT" "$FLEET_SLOT" --inside-scope
fi
test ! -e "$runtime/author-events.typescript"
test ! -e "$runtime/author-events.timing"
cd "$FLEET_WORKSPACE"
printf -v command '%q ' bwrap --bind / / --proc /proc --dev-bind /dev /dev --ro-bind "$FLEET_INPUT" "$FLEET_INPUT" --bind "$FLEET_WORKSPACE/output/native-sessions" /home/ts/.codex/sessions "${history_mount_argv[@]}" --tmpfs /home/ts/.codex/archived_sessions --tmpfs /home/ts/.codex/skills --tmpfs /home/ts/.codex/memories --ro-bind /dev/null /home/ts/.agent-comms/.pi/APPEND_SYSTEM.md --ro-bind "$config" /home/ts/.codex/config.toml --ro-bind "$skill" /home/ts/.codex/skills/use-openhcs --chdir "$FLEET_WORKSPACE" "$cli" exec --json --skip-git-repo-check --color never -o output/FINAL.rst "${history_argv[@]}" "Read TASK.rst in the current workspace. Complete the released public analysis autonomously within its recorded resource, evidence and time bounds; freeze and report the final attempted pipeline even on rejection or abstention."
exec /usr/bin/flock --nonblock -E 75 "$FLEET_RUN_ROOT/$FLEET_SLOT/author.lock" /usr/bin/script --quiet --flush --return --log-out "$runtime/author-events.typescript" --log-timing "$runtime/author-events.timing" --command "$command"
