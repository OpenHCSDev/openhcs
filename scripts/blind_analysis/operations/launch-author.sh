#!/bin/bash
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "${1:?root}" "${2:?slot}"
config=$(jq -er '.author_config' "$FLEET_RUN_ROOT/program.json")
cli=$(jq -er '.cli' "$FLEET_RUN_ROOT/program.json")
prompt="Read TASK.rst in the current workspace. Complete the released public analysis autonomously within its recorded resource, evidence and time bounds; freeze and report the final attempted pipeline even on rejection or abstention."
# The CLI's last answer is controller evidence, not an authored science report.
# Use the existing recorder namespace for fresh and recovery observations alike.
final_message="$FLEET_RECORD_RUNTIME/author-final-answer.rst"
if [[ -n "${FLEET_RECOVERY_OBSERVATION:-}" ]]; then
  prompt="Continue this saved analysis context after the CLI interruption; this is a recorded continuation, not a new fresh autonomous pass. Original author and stdio client journals have closed; their originals and scientific outputs remain immutable. Original native runtimes remain alive. Do not start a native runtime or replay any UNKNOWN input. Start exactly one replacement recorded interactive client using: FLEET_RECOVERY_OBSERVATION=$FLEET_RECOVERY_OBSERVATION bash $FLEET_OPERATIONS/recorded-mcp.sh $FLEET_ROOT $FLEET_SLOT reconnect01. Keep that original tool handle. First use ordinary health and openhcs_observe_owned_runtime with the exact original RuntimeBootstrapHandle retained in your journal/files, then read-only reconcile pending jobs and viewer identities. No port-based adoption or synthetic handle. Resume only known-disposed work and unfinished QA through this retained runtime. Preserve interruption, original first-MCP clock and source/bundle/skill identities; record this operational revision separately. Use the same recovery observation environment and operations path for subsequent resource observations. No model/provider switch, no changed science settings or external answers supplied by this intervention. Complete your own reasoning/QA and close exact owned processes when done. Original TASK.rst objective remains; do not overwrite original journals or original FINAL files."
fi
skill="$FLEET_INSTALL/openhcs/agent/resources/knowledge/packaging/codex/openhcs/skills/use-openhcs"
# Native context is declared once on the immutable member. A retained child
# must already exist in this run's isolated native session namespace.
history_projection_json=$(fleet_author_context)
mapfile -t history_argv < <(jq -r '.argv[]' <<< "$history_projection_json")
history_mount_argv=()
while IFS= read -r ancestor_output; do
  history_mount_argv+=(--ro-bind "$ancestor_output" "$ancestor_output")
done < <(jq -r '.read_roots[]' <<< "$history_projection_json")
# Paginated native children retain ancestor rollouts at the canonical sessions
# path. Their immutable writer owners supply the files; Codex owns decoding.
while IFS= read -r ancestor_root; do
  test -d "$ancestor_root"
  while IFS= read -r -d '' ancestor; do
    history_mount_argv+=(--ro-bind "$ancestor" "$ancestor")
    history_mount_argv+=(--ro-bind "$ancestor" "/home/ts/.codex/sessions/${ancestor#"$ancestor_root"/}")
  done < <(find "$ancestor_root" -type f -name 'rollout-*.jsonl' -size +0c -print0)
done < <(jq -r '.history_roots[]' <<< "$history_projection_json")
if [[ "${3:-}" == --preflight ]]; then
  printf 'root=%s slot=%s cwd=%s config=%s skill=%s cli=%s unit=%s history_args=%s\n' "$FLEET_ROOT" "$FLEET_SLOT" "$FLEET_WORKSPACE" "$config" "$skill" "$cli" "$FLEET_UNIT-author" "$(jq -c '.argv' <<< "$history_projection_json")"
  printf 'model=%s provider=%s effort=%s cpu=%s display=%s native=%s viewer=%s session-bind=%s\n' "$(jq -er '.model' "$FLEET_RUN_ROOT/program.json")" "$(jq -er '.model_provider' "$FLEET_RUN_ROOT/program.json")" "$(jq -er '.reasoning_effort' "$FLEET_RUN_ROOT/program.json")" "$FLEET_CPU" "$FLEET_DISPLAY" "$FLEET_NATIVE" "$FLEET_VIEWER" "$FLEET_WORKSPACE/output/native-sessions"
  printf 'readonly_history_args='; printf '%q ' "${history_mount_argv[@]}"; printf '\n'
  printf 'readonly_ancestry_outputs=%s\n' "$(jq -c '.read_roots' <<< "$history_projection_json")"
  printf 'input=%s read=%s:%s:%s:%s write=%s:%s scratch=%s workers=%s\n' "$FLEET_INPUT" "$FLEET_INPUT" "$FLEET_WORKSPACE/output" "$FLEET_ARTIFACT_ROOT" "$FLEET_INSTALL/openhcs/agent/resources/knowledge" "$FLEET_WORKSPACE/output" "$FLEET_ARTIFACT_ROOT" "$FLEET_SCRATCH" "$(jq -er '.proposed_resource_envelope.science_workers_per_author' "$FLEET_RUN_ROOT/program.json")"
  exit
fi
# A scientific brief grants an author turn; engineering permissions have none.
jq -e --arg slot "$FLEET_SLOT" '.authors[] | select(.slot==$slot) |
  .brief | type=="string" and length>0' "$FLEET_RUN_ROOT/program.json" >/dev/null
test -f "$FLEET_RUN_ROOT/READY-FREEZE.sha256"
(cd "$FLEET_RUN_ROOT"; sha256sum --check --quiet READY-FREEZE.sha256)
mkdir -p "$FLEET_WORKSPACE/output/runtime" "$FLEET_WORKSPACE/output/native-sessions"
fleet_require_artifact_destination "$FLEET_SLOT"
runtime="$FLEET_RECORD_RUNTIME"
mkdir -p "$runtime"
if [[ "${3:-}" != --inside-scope ]]; then
  fleet_require_joint_slice
  admission=replacement
  observation=author_launch
  if [[ -n "${FLEET_RECOVERY_OBSERVATION:-}" ]]; then
    admission=full
    observation="author_launch_$FLEET_RECOVERY_OBSERVATION"
  fi
  bash "$FLEET_OPERATIONS/resource-check.sh" "$FLEET_ROOT" "$FLEET_SLOT" "$observation" "$admission"
  cpu=$(jq -er '.proposed_resource_envelope.cpu_quota_per_author_percent' "$FLEET_RUN_ROOT/program.json")
  exec /usr/bin/systemd-run --user --scope --slice="$FLEET_SLICE" --unit="$FLEET_AUTHOR_UNIT" -p CPUQuota="${cpu}%" /usr/bin/taskset -c "$FLEET_CPU" /bin/bash "$FLEET_OPERATIONS/launch-author.sh" "$FLEET_ROOT" "$FLEET_SLOT" --inside-scope
fi
test ! -e "$runtime/author-events.typescript"
test ! -e "$runtime/author-events.timing"
cd "$FLEET_WORKSPACE"
printf -v command '%q ' bwrap --bind / / --proc /proc --dev-bind /dev /dev --ro-bind "$FLEET_INPUT" "$FLEET_INPUT" --bind "$FLEET_WORKSPACE/output/native-sessions" /home/ts/.codex/sessions "${history_mount_argv[@]}" --tmpfs /home/ts/.codex/archived_sessions --tmpfs /home/ts/.codex/skills --tmpfs /home/ts/.codex/memories --ro-bind /dev/null /home/ts/.agent-comms/.pi/APPEND_SYSTEM.md --ro-bind "$config" /home/ts/.codex/config.toml --ro-bind "$skill" /home/ts/.codex/skills/use-openhcs --chdir "$FLEET_WORKSPACE" "$cli" exec --json --skip-git-repo-check --color never -o "$final_message" "${history_argv[@]}" "$prompt"
exec /usr/bin/flock --nonblock -E 75 "$FLEET_RUN_ROOT/$FLEET_SLOT/author.lock" /usr/bin/script --quiet --flush --return --log-out "$runtime/author-events.typescript" --log-timing "$runtime/author-events.timing" --command "$command"
