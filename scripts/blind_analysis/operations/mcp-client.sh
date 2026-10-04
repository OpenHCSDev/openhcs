#!/bin/bash
# Internal recorded-client performer; admission belongs to recorded-mcp.sh.
set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/slot-env.sh" "${1:?root}" "${2:?slot}"
DISPLAY=:$FLEET_DISPLAY /usr/bin/xprop -root _NET_SUPPORTING_WM_CHECK _NET_SUPPORTED > "$FLEET_WORKSPACE/output/runtime/wm-before-mcp.txt"
rg -q WINDOW "$FLEET_WORKSPACE/output/runtime/wm-before-mcp.txt"
test -f "$FLEET_INSTALL/openhcs/mcp/server.py"
unset OPENHCS_METADATA_FILENAME OPENHCS_UI_BRIDGE_DESCRIPTOR
export PYTHONPATH="$FLEET_INSTALL" DISPLAY=:$FLEET_DISPLAY QT_QPA_PLATFORM=xcb LIBGL_ALWAYS_SOFTWARE=1
export OPENHCS_UI_BRIDGE_DESCRIPTOR="$FLEET_WORKSPACE/output/no-attached-ui.json"
export POLYSTORE_METADATA_FILENAME=generic-private.json PYTHONDONTWRITEBYTECODE=1 OPENHCS_CPU_ONLY=true OPENHCS_HEADLESS=true CUDA_VISIBLE_DEVICES=
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1 JAX_PLATFORMS=cpu NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 BLIS_NUM_THREADS=1
export POLYSTORE_IMAGEJ_CACHE_ROOT=/home/ts/.cache/polystore/imagej POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
scratch="$FLEET_WORKSPACE/output/runtime/scratch"
export XDG_CACHE_HOME="$scratch/cache" XDG_CONFIG_HOME="$scratch/config" XDG_DATA_HOME="$scratch/data" XDG_STATE_HOME="$scratch/state" XDG_RUNTIME_DIR="$scratch/runtime" TMPDIR="$scratch" NUMBA_CACHE_DIR="$scratch/numba" MPLCONFIGDIR="$scratch/matplotlib" OPENHCS_UI_CONFIG_CACHE_FILE="$scratch/config/ui-config-cache.json"
reservations="/home/ts/.openhcs/tcp/$FLEET_NATIVE.startup.lock:/home/ts/.openhcs/tcp/$FLEET_NATIVE_ACK.startup.lock:/home/ts/.openhcs/tcp/$FLEET_VIEWER.startup.lock:/home/ts/.openhcs/tcp/$FLEET_VIEWER_ACK.startup.lock"
export OPENHCS_AGENT_READ_ROOTS="$FLEET_WORKSPACE/output:$scratch:$FLEET_INPUT:$FLEET_INSTALL/openhcs/agent/resources/knowledge:$reservations"
export OPENHCS_AGENT_WRITE_ROOTS="$FLEET_WORKSPACE/output:$scratch:$reservations"
mkdir -p "$XDG_CACHE_HOME" "$XDG_CONFIG_HOME" "$XDG_DATA_HOME" "$XDG_STATE_HOME" "$XDG_RUNTIME_DIR" "$NUMBA_CACHE_DIR" "$MPLCONFIGDIR"
chmod 700 "$XDG_RUNTIME_DIR"
cap=$(fleet_process_limit_mib mcp)
test "$cap" -gt 0
cpu=$(jq -er '.proposed_resource_envelope.cpu_quota_per_author_percent' <<< "$FLEET_RUN_PROGRAM")
test ! -e "$FLEET_WORKSPACE/output/runtime/first-mcp-started.epoch"
date -u +%s | tee "$FLEET_WORKSPACE/output/runtime/first-mcp-started.epoch"
exec /usr/bin/env XDG_RUNTIME_DIR=/run/user/1000 /usr/bin/systemd-run --user --scope --slice="$FLEET_SLICE" --unit="$FLEET_UNIT-mcp" -p MemoryMax="${cap}M" -p MemorySwapMax=0 -p CPUQuota="${cpu}%" /usr/bin/env XDG_RUNTIME_DIR="$scratch/runtime" /usr/bin/taskset -c "$FLEET_CPU" "$FLEET_PYTHON" -B -m openhcs.mcp.dev_client --no-resident --timeout-seconds 10 shell --no-prompt
