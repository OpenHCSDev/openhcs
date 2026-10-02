#!/bin/sh
# Read-only existing dependency admission; never activate the installed target.
set -eu
source_root=/home/ts/wt/openhcs-knowledge-declaration-source-376-20261001
paired_site=/home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/lib/python3.12/site-packages
backing_site=/home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages
export PYTHONPATH="$source_root:$paired_site:$backing_site"
export PYTHONDONTWRITEBYTECODE=1 PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1 NUMBA_NUM_THREADS=1
cd "$source_root"
exec /usr/bin/time -v systemd-run --user --scope --unit="$1" \
    -p MemoryMax=512M -p MemorySwapMax=0 -p AllowedCPUs=0 \
    timeout 60 /home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/bin/python \
    -B validation/run-s1-sampling-tests.py "$@"
