#!/bin/bash
set -euo pipefail
# Explicit parent authorization: one install into this new unused private target.
unset PYTHONPATH
export PYTHONDONTWRITEBYTECODE=1 PIP_NO_INDEX=1 PIP_DISABLE_PIP_VERSION_CHECK=1
export UV_OFFLINE=1 POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
export TMPDIR=/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/engineering394404-wheel-94ee-dd324-20261002/scratch/tmp
wheel_path=/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/engineering394404-wheel-94ee-dd324-20261002/wheels/openhcs-0.8.7-cp311-abi3-linux_x86_64.whl
target_path=/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/engineering394404-wheel-94ee-dd324-20261002/target-reviewed-f236ccfb-20261002
test "$(sha256sum "$wheel_path" | cut -d ' ' -f 1)" = f236ccfb557c2c08f5ac8c174fd0e5350ad4c9f552fb02b1d302b46d52dd8c60
test ! -e "$target_path"
mkdir -- "$target_path"
exec /home/ts/wt/basicpy-live-candidate-20260930/.venv/bin/python -B -m pip install \
  --no-deps --no-index --no-compile --no-cache-dir \
  --target "$target_path" "$wheel_path"
