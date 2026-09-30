#!/bin/sh
# Parent-owned source-qualified live acceptance; never touches desktop :0.
set -eu
export PYTHONPATH=/home/ts/wt/openhcs-viewer-reset-parent-integration-20260930
export PYTHONDONTWRITEBYTECODE=1 PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
export OPENHCS_CPU_ONLY=true OPENHCS_SUBPROCESS_NO_GPU=1 POLYSTORE_SUBPROCESS_NO_GPU=1
export OPENHCS_USE_THREADING=true OPENHCS_HEADLESS=true CUDA_VISIBLE_DEVICES=
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1
export QT_QPA_PLATFORM=xcb DISPLAY=:91 LIBGL_ALWAYS_SOFTWARE=1
export POLYSTORE_IMAGEJ_CACHE_ROOT=/home/ts/.cache/polystore/imagej
export POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
export XDG_CACHE_HOME=/home/ts/.cache/agent-scratch/vr308-parent/cache
export XDG_CONFIG_HOME=/home/ts/.cache/agent-scratch/vr308-parent/config
export XDG_DATA_HOME=/home/ts/.cache/agent-scratch/vr308-parent/data
export XDG_STATE_HOME=/home/ts/.cache/agent-scratch/vr308-parent/state
export XDG_RUNTIME_DIR=/home/ts/.cache/agent-scratch/vr308-parent/runtime
export TMPDIR=/home/ts/.cache/agent-scratch/vr308-parent
export NUMBA_CACHE_DIR=/home/ts/.cache/agent-scratch/vr308-parent/numba
export MPLCONFIGDIR=/home/ts/.cache/agent-scratch/vr308-parent/matplotlib
export OPENHCS_UI_CONFIG_CACHE_FILE=/home/ts/.cache/agent-scratch/vr308-parent/ui_config.config
export OPENHCS_AGENT_READ_ROOTS=/home/ts/wt/openhcs-viewer-reset-parent-integration-20260930:/home/ts/wt/openhcs-issue-batch-20260929/viewer-reset-parent-20260930:/home/ts/.cache/agent-scratch/vr308-parent:/home/ts/.openhcs/tcp/5995.startup.lock:/home/ts/.openhcs/tcp/6995.startup.lock
export OPENHCS_AGENT_WRITE_ROOTS=/home/ts/wt/openhcs-issue-batch-20260929/viewer-reset-parent-20260930:/home/ts/.cache/agent-scratch/vr308-parent:/home/ts/.openhcs/tcp/5995.startup.lock:/home/ts/.openhcs/tcp/6995.startup.lock
cd /home/ts/wt/openhcs-viewer-reset-parent-integration-20260930
exec /home/ts/code/projects/openhcs/.venv/bin/python -B "$@"
