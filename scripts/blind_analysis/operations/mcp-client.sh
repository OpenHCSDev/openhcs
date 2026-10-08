#!/bin/bash
# Internal recorded-client performer; admission belongs to recorded-mcp.sh.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "${1:?root}" "${2:?slot}"
mode=${3:-author}
case "$mode" in
  author) ;;
  --qualify) FLEET_CLIENT_UNIT+="-qualification" ;;
  *) exit 64 ;;
esac
if [[ "$mode" == author && -z "${FLEET_RECOVERY_OBSERVATION:-}" ]]; then
  DISPLAY=:$FLEET_DISPLAY /usr/bin/xprop -root _NET_SUPPORTING_WM_CHECK _NET_SUPPORTED > "$FLEET_WORKSPACE/output/runtime/wm-before-mcp.txt"
  rg -q WINDOW "$FLEET_WORKSPACE/output/runtime/wm-before-mcp.txt"
fi
# Retained native observation uses the headless stdio server. No GUI-helper
# startup or VNC access is implied by replacing its closed controller.
test -f "$FLEET_INSTALL/openhcs/mcp/server.py"
unset OPENHCS_METADATA_FILENAME OPENHCS_UI_BRIDGE_DESCRIPTOR
export DISPLAY=:$FLEET_DISPLAY QT_QPA_PLATFORM=xcb LIBGL_ALWAYS_SOFTWARE=1
export OPENHCS_UI_BRIDGE_DESCRIPTOR="$FLEET_WORKSPACE/output/no-attached-ui.json"
export POLYSTORE_METADATA_FILENAME=generic-private.json PYTHONDONTWRITEBYTECODE=1 OPENHCS_CPU_ONLY=true OPENHCS_HEADLESS=true CUDA_VISIBLE_DEVICES=
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1 JAX_PLATFORMS=cpu NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 BLIS_NUM_THREADS=1
export POLYSTORE_IMAGEJ_CACHE_ROOT=/home/ts/.cache/polystore/imagej POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
fleet_require_artifact_destination "$FLEET_SLOT"
scratch="$FLEET_SCRATCH"
# The existing ancestry owner checks predecessor units on the user bus. Resolve
# custody before replacing the user runtime directory with private OpenHCS IPC.
context=$(fleet_author_context)
ancestry=$(jq -r '.read_roots|join(":")' <<< "$context")
# NTFS carries scientific payloads, not private config or POSIX0700 IPC runtime.
if [[ "$mode" == --qualify ]]; then
  control="$FLEET_RUN_ROOT/launcher-qualification-control"
  scratch="$control/scratch"
else
  control="$FLEET_WORKSPACE/output/runtime"
fi
export XDG_CACHE_HOME="$scratch/cache" XDG_CONFIG_HOME="$control/config" XDG_DATA_HOME="$control/data" XDG_STATE_HOME="$control/state" XDG_RUNTIME_DIR="$control/xdg-runtime" TMPDIR="$scratch" NUMBA_CACHE_DIR="$scratch/numba" MPLCONFIGDIR="$scratch/matplotlib" OPENHCS_UI_CONFIG_CACHE_FILE="$control/config/ui-config-cache.json"
reservations="/home/ts/.openhcs/tcp/$FLEET_NATIVE.startup.lock:/home/ts/.openhcs/tcp/$FLEET_NATIVE_ACK.startup.lock:/home/ts/.openhcs/tcp/$FLEET_VIEWER.startup.lock:/home/ts/.openhcs/tcp/$FLEET_VIEWER_ACK.startup.lock"
export OPENHCS_AGENT_READ_ROOTS="$FLEET_WORKSPACE/output:$FLEET_ARTIFACT_ROOT:$control:$scratch:$FLEET_INPUT:$FLEET_KNOWLEDGE_READ_ROOTS:$reservations${ancestry:+:$ancestry}"
export OPENHCS_AGENT_WRITE_ROOTS="$FLEET_WORKSPACE/output:$FLEET_ARTIFACT_ROOT:$control:$scratch:$reservations"
mkdir -p "$XDG_CACHE_HOME" "$XDG_CONFIG_HOME" "$XDG_DATA_HOME" "$XDG_STATE_HOME" "$XDG_RUNTIME_DIR" "$NUMBA_CACHE_DIR" "$MPLCONFIGDIR"
chmod 700 "$XDG_RUNTIME_DIR"
cpu=$(jq -er '.proposed_resource_envelope.cpu_quota_per_author_percent' <<< "$FLEET_RUN_PROGRAM")
if [[ "$mode" == author && -z "${FLEET_RECOVERY_OBSERVATION:-}" ]]; then
  test ! -e "$FLEET_WORKSPACE/output/runtime/first-mcp-started.epoch"
  date -u +%s | tee "$FLEET_WORKSPACE/output/runtime/first-mcp-started.epoch"
fi
if [[ "$mode" == --qualify ]]; then
  "$FLEET_PYTHON" -B - <<'PY'
import hashlib, importlib, json, os
from openhcs.agent.skill_sync import installed_skill_bundle
skill, = (p for p in installed_skill_bundle().skill_roots() if p.name == "use-openhcs")
print(json.dumps({
    "python_source_roots": os.environ["PYTHONPATH"].split(":"),
    "module_origins": {n: importlib.import_module(n).__file__ for n in (
        "openhcs", "objectstate", "polystore", "arraybridge", "metaclass_registry",
        "pycodify", "pyqt_reactive", "python_introspect", "zmqruntime")},
    "skill": str(skill),
    "skill_sha256": hashlib.sha256((skill / "SKILL.md").read_bytes()).hexdigest(),
    "read_roots": os.environ["OPENHCS_AGENT_READ_ROOTS"].split(":"),
}, indent=2), flush=True)
PY
fi
exec /usr/bin/env XDG_RUNTIME_DIR=/run/user/1000 /usr/bin/systemd-run --user --scope --slice="$FLEET_SLICE" --unit="$FLEET_CLIENT_UNIT" -p CPUQuota="${cpu}%" /usr/bin/env XDG_RUNTIME_DIR="$XDG_RUNTIME_DIR" /usr/bin/taskset -c "$FLEET_CPU" "$FLEET_PYTHON" -B -m openhcs.mcp.dev_client --no-resident --timeout-seconds 10 shell --no-prompt
