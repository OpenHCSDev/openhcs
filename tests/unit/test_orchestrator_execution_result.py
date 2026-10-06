from __future__ import annotations

import pickle
from types import MappingProxyType

import pytest

from openhcs.core.orchestrator.compiled_plate_execution import (
    CompiledPlateExecutionResults,
)

from openhcs.core.orchestrator.execution_result import ExecutionResult


def test_execution_result_transport_preserves_mapping_proxy_metadata() -> None:
    result = ExecutionResult.success(axis_id="W001")
    payload = {"result": result, "metadata": MappingProxyType({"well": "W001"})}

    restored = pickle.loads(pickle.dumps(payload))

    assert restored["result"].is_success()
    assert restored["metadata"] == {"well": "W001"}
    assert isinstance(restored["metadata"], MappingProxyType)


@pytest.mark.parametrize("failed", [False, True])
def test_plate_terminal_outcome_preserves_individual_axes(failed: bool) -> None:
    successful = ExecutionResult.success("A01")
    other = (
        ExecutionResult.error("A02", error_message="producer lineage missing")
        if failed
        else ExecutionResult.success("A02")
    )
    results = CompiledPlateExecutionResults({"A01": successful, "A02": other})
    assert results.is_success() is not failed
    if failed:
        with pytest.raises(RuntimeError, match="A02: error: producer lineage missing"):
            results.require_success()
    else:
        results.require_success()
    assert results["A01"] is successful
    assert results["A02"] is other
