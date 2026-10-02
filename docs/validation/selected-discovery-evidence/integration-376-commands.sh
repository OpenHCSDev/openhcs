#!/bin/sh
# Source-only receipt commands, run individually and serially. No installs.
set -eu
export PYTHONDONTWRITEBYTECODE=1 PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
export OPENHCS_CPU_ONLY=true POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1
export XDG_CACHE_HOME=/home/ts/.cache/agent-scratch/knowledge-selected-integration-376-20261001/cache
case "$1" in
  tests)
    cd /home/ts/wt/openhcs-knowledge-declaration-source-376-20261001
    exec /usr/bin/time -v timeout 60s taskset -c 0 \
      /home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/bin/python -B \
      docs/validation/knowledge-selected-source-tests.py \
      tests/unit/agent/test_knowledge_lazy_conversion_boundary.py \
      tests/unit/agent/test_declaration_selected_discovery.py \
      /home/ts/wt/metaclass-registry-selected-discovery-376-20261001/tests/test_selected_discovery.py \
      /home/ts/wt/metaclass-registry-selected-discovery-376-20261001/tests/test_discovery.py \
      /home/ts/wt/metaclass-registry-selected-discovery-376-20261001/tests/test_core.py \
      --basetemp=/home/ts/.cache/agent-scratch/knowledge-selected-integration-376-20261001/pytest \
      -k 'not canonical_custom'
    ;;
  r0-openhcs)
    cd /home/ts/wt/openhcs-knowledge-declaration-source-376-20261001
    exec /usr/bin/time -v timeout 60s taskset -c 0 \
      /home/ts/.local/share/uv/python/cpython-3.14-linux-x86_64-gnu/bin/python3.14 -I -B -c \
      'import sys;sys.path[:0]=["/home/ts/wt/comms-ratchet-pinned-ui348-20261001/src","/home/ts/wt/basicpy-live-candidate-20260930/.venv/lib/python3.12/site-packages"];from agent_comms.debt_ratchet import main;sys.argv=["agent-comms-ratchet","--root","openhcs","--base",sys.argv[1],"--head","HEAD"];sys.exit(main())' "$2"
    ;;
  r0-dependency)
    cd /home/ts/wt/metaclass-registry-selected-discovery-376-20261001
    exec /usr/bin/time -v timeout 60s taskset -c 0 \
      /home/ts/.local/share/uv/python/cpython-3.14-linux-x86_64-gnu/bin/python3.14 -I -B -c \
      'import sys;sys.path[:0]=["/home/ts/wt/comms-ratchet-pinned-ui348-20261001/src","/home/ts/wt/basicpy-live-candidate-20260930/.venv/lib/python3.12/site-packages"];from agent_comms.debt_ratchet import main;sys.argv=["agent-comms-ratchet","--root","src/metaclass_registry","--base",sys.argv[1],"--head","HEAD"];sys.exit(main())' "$2"
    ;;
  *) exit 2 ;;
esac
# Outer caller uses systemd-run --user --scope -p MemoryMax=512M
# -p MemorySwapMax=0 -p CPUQuota=100% -- sh <this-file> <mode> [base].
