#!/usr/bin/env bash
set -eu
label="$1"
shift
export PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=. PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
export OPENHCS_CPU_ONLY=true OPENHCS_SUBPROCESS_NO_GPU=1 POLYSTORE_SUBPROCESS_NO_GPU=1
export OPENHCS_USE_THREADING=true OPENHCS_HEADLESS=true CUDA_VISIBLE_DEVICES=
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1
export NUMBA_DISABLE_JIT=1 POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
export XDG_CACHE_HOME=/home/ts/.cache/agent-scratch/artifact-publication-315-20260930/cache
export NUMBA_CACHE_DIR="$XDG_CACHE_HOME/numba" MPLCONFIGDIR="$XDG_CACHE_HOME/matplotlib"
/usr/bin/time -v timeout 60s /home/ts/code/projects/openhcs/.venv/bin/python -m pytest \
  -o addopts='' -q "$@" \
  --basetemp="/home/ts/.cache/agent-scratch/artifact-publication-315-20260930/$label"
