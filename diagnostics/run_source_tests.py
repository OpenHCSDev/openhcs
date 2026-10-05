"""Run owned source checks using only the unchanged installed native artifact."""

import os
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
root = Path(os.environ.get("SOURCE_BASELINE_ROOT", str(root))).resolve()
sys.path.insert(0, str(root))
import openhcs.core

artifact_root = Path(
    "/home/ts/wt/openhcs-s1-installed-parent-20261001/.venv/lib/python3.12/site-packages/openhcs/core"
)
openhcs.core.__path__.append(str(artifact_root))
print("source root:", root, flush=True)
print("native artifact:", artifact_root / "_tabular_native.abi3.so", flush=True)
baseline_ref = os.environ.get("BASELINE_EXECUTOR_REF")
if baseline_ref:
    import openhcs.interop.cellprofiler.runtime.function_contract_execution as executor_module

    source = subprocess.check_output(
        [
            "git", "show",
            f"{baseline_ref}:openhcs/interop/cellprofiler/runtime/function_contract_execution.py",
        ],
        cwd=root,
    )
    print("baseline executor ref:", baseline_ref, flush=True)
    exec(
        compile(source, f"git:{baseline_ref}:function_contract_execution.py", "exec"),
        executor_module.__dict__,
    )
import pytest

raise SystemExit(pytest.main(sys.argv[1:]))
