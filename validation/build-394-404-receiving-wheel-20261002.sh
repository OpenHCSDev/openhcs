#!/bin/bash
set -euo pipefail
# Reuse the original ordinary setuptools/PEP517 owner and installed build tools.
# No installation, dependency resolution, isolation, package import or native UI.
unset PYTHONPATH
export PYTHONDONTWRITEBYTECODE=1 OPENHCS_CPU_ONLY=true CUDA_VISIBLE_DEVICES=
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1
export MAX_JOBS=1 CARGO_BUILD_JOBS=1
export PIP_NO_INDEX=1 PIP_DISABLE_PIP_VERSION_CHECK=1 UV_OFFLINE=1
export POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
export XDG_CACHE_HOME=/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/engineering394404-wheel-94ee-dd324-20261002/scratch/cache
export TMPDIR=/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/engineering394404-wheel-94ee-dd324-20261002/scratch/tmp
cd /home/ts/wt/openhcs-knowledge-lazy-conversion-20261001
git merge-base --is-ancestor 94ee1079d22540f9b5ed48b69481d7e7ab51095d HEAD
git diff --exit-code 94ee1079d22540f9b5ed48b69481d7e7ab51095d -- openhcs benchmark scripts pyproject.toml setup.py MANIFEST.in
exec /home/ts/wt/basicpy-live-candidate-20260930/.venv/bin/python -B -m build \
  --wheel --no-isolation \
  --outdir /home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/engineering394404-wheel-94ee-dd324-20261002/wheels
