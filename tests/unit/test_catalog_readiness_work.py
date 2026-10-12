"""Catalog readiness does no per-callable work; first use does one callable's."""

from __future__ import annotations

import json
import subprocess
import sys
import textwrap

_PROBE = textwrap.dedent(
    """
    import json

    from numba.core import event

    listener = event.RecordingListener()
    event.register("numba:compile", listener)

    from openhcs.core.callable_contract import CallableContract, CallableProjection
    from openhcs.core.processing_preparation import PreparationOperation
    from openhcs.processing.backends.lib_registry.registry_service import RegistryService


    def compiled_modules():
        return sorted({
            item.data["dispatcher"].py_func.__module__
            for _, item in listener.buffer
            if item.data["dispatcher"].py_func.__module__.startswith("openhcs.")
        })


    metadata = RegistryService.prepare_in_current_process()
    report = {
        "callables": len(metadata),
        "ready_compilations": len(listener.buffer),
        "ready_operations": len(PreparationOperation._completed),
    }
    used = next(
        item.func for item in metadata.values()
        if item.func.__name__ == "create_composite"
        and item.func.__module__.endswith("numpy_processor")
    )
    CallableContract.from_prepared_callable(used)
    report["use_targets"] = len(CallableProjection.from_callable(used).prepare_targets())
    report["use_operations"] = len(PreparationOperation._completed)
    report["use_compiled_modules"] = compiled_modules()
    print("REPORT " + json.dumps(report))
    """
)


def test_readiness_compiles_nothing_and_first_use_prepares_one_callable(tmp_path):
    """Count the work, not the seconds: 665 kernel compilations once ran here."""
    completed = subprocess.run(
        [sys.executable, "-c", _PROBE],
        capture_output=True,
        text=True,
        check=False,
        cwd=tmp_path,
    )
    assert completed.returncode == 0, completed.stderr[-4000:]
    report = json.loads(
        next(
            line for line in completed.stdout.splitlines() if line.startswith("REPORT ")
        )[len("REPORT "):]
    )

    assert report["callables"] > 0
    assert report["ready_compilations"] == 0
    assert report["ready_operations"] == 0
    # Operations are shared per module: never more than the callable's targets.
    assert 0 < report["use_operations"] <= report["use_targets"]
    assert set(report["use_compiled_modules"]) <= {
        "openhcs.processing.backends.processors.numpy_processor"
    }
