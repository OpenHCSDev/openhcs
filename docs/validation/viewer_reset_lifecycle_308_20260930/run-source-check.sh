#!/bin/sh
# Issue308 owner scratch only; no server, scientific data, GL canvas or downloads.
set -eu
cd /home/ts/wt/openhcs-viewer-reset-lifecycle-308-20260930
export PYTHONPATH="$PWD" PYTHONDONTWRITEBYTECODE=1 PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
export OPENHCS_CPU_ONLY=true OPENHCS_SUBPROCESS_NO_GPU=1 POLYSTORE_SUBPROCESS_NO_GPU=1
export OPENHCS_USE_THREADING=true OPENHCS_HEADLESS=true CUDA_VISIBLE_DEVICES=""
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1
export NUMBA_DISABLE_JIT=1
export QT_QPA_PLATFORM=offscreen POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
export XDG_CACHE_HOME=/home/ts/.cache/agent-scratch/viewer-reset-lifecycle-308-20260930/cache
export NUMBA_CACHE_DIR="$XDG_CACHE_HOME/numba" MPLCONFIGDIR="$XDG_CACHE_HOME/matplotlib"
exec /usr/bin/time -v /home/ts/code/projects/openhcs/.venv/bin/python -m pytest \
    -o addopts='' -o cache_dir="$XDG_CACHE_HOME/pytest" --basetemp=/home/ts/.cache/agent-scratch/viewer-reset-lifecycle-308-20260930/pytest \
    "$@"
