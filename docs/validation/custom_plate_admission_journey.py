"""Independent installed registration/reload journey; no native or science job.

Run with a private wheel target on PYTHONPATH and owned XDG_DATA_HOME/cache.
"""
from __future__ import annotations

import inspect
import json
from pathlib import Path
import sys

import openhcs
from openhcs.core.callable_contract import CallableContract, FunctionStepExecutionScope
from openhcs.core.function_reference import FunctionReferenceTransportAuthority
from openhcs.core.pipeline.funcstep_contract_validator import FuncStepContractValidator
from openhcs.core.runtime_stores import RuntimeArtifactBatch
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import CustomFunctionRuntimeRegistry
from openhcs.processing.custom_functions.validation import ValidationError
from openhcs.processing.func_registry import get_function


SOURCE = '''from openhcs.core.artifacts import ArtifactSpec, SpecialArtifactType
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.pipeline.function_contracts import (
    artifact_outputs, execution_scope, runtime_bound_parameters,
)
from openhcs.core.runtime_stores import RuntimeArtifactBatch

def _helper():
    return b"independent engineering fixture"

@execution_scope(FunctionStepExecutionScope.PLATE)
@runtime_bound_parameters(RuntimeArtifactBatch)
@artifact_outputs(ArtifactSpec.output("EngineeringBundle", SpecialArtifactType))
def engineering_plate_abi(*, artifact_batch: RuntimeArtifactBatch):
    return {"engineering.txt": _helper()}
'''


def main() -> None:
    expected_target = Path(sys.argv[1]).resolve()
    assert Path(openhcs.__file__).resolve().is_relative_to(expected_target)
    manager = CustomFunctionManager()
    assert not tuple(manager.storage_dir.glob("*.py")), "Use a NEW owned fixture root."
    [function] = manager.register_from_code(SOURCE, clear_caches=False, emit_signal=False)
    key = "openhcs:engineering_plate_abi"
    assert get_function(key) is function
    contract = CallableContract.from_callable(function)
    assert contract.execution_scope is FunctionStepExecutionScope.PLATE
    assert not contract.declared_memory_types
    assert contract.processing_contract is None
    FuncStepContractValidator.validate_plate_callable_contracts((contract,), "engineering")
    batch = RuntimeArtifactBatch(
        input_specs=(), records_by_axis={},
        source_image_set_identity_policy=SourceImageSetIdentityPolicy(),
    )
    assert function(artifact_batch=batch) == {"engineering.txt": b"independent engineering fixture"}
    source_path = manager.source_path_for_function(function)
    assert source_path.read_text() == SOURCE
    [info] = manager.list_custom_functions()
    assert info.memory_type is None and info.backend_label == "plate"
    assert info.contract.processing_contract is None
    reference = FunctionReferenceTransportAuthority.function_reference(function)
    assert reference.resolve() is function
    for replacement in (
        "artifact_batch: RuntimeArtifactBatch = None",
        "artifact_batch: int",
        "image, artifact_batch: RuntimeArtifactBatch",
    ):
        invalid = SOURCE.replace("engineering_plate_abi", "engineering_invalid_abi")
        invalid = invalid.replace("*, artifact_batch: RuntimeArtifactBatch", replacement)
        try:
            manager.register_from_code(invalid, clear_caches=False, emit_signal=False)
        except ValidationError:
            pass
        else:
            raise AssertionError("Invalid ABI was admitted")
        assert not manager.source_path_for_name(manager.storage_dir, "engineering_invalid_abi").exists()
        assert "engineering_invalid_abi" not in CustomFunctionRuntimeRegistry.metadata_by_name()
    CustomFunctionRuntimeRegistry.clear()
    assert manager.load_custom_function("engineering_plate_abi", clear_caches=False) == 1
    reloaded = get_function(key)
    reloaded_contract = CallableContract.from_callable(reloaded)
    FuncStepContractValidator.validate_plate_callable_contracts((reloaded_contract,), "reloaded")
    assert reloaded_contract.processing_contract is None
    assert reloaded(artifact_batch=batch) == function(artifact_batch=batch)
    manager.update_custom_function("engineering_plate_abi", SOURCE.replace("fixture", "replacement"))
    try:
        reference.resolve()
    except RuntimeError:
        pass
    else:
        raise AssertionError("Changed-source reference retained authority")
    assert get_function(key)(artifact_batch=batch)["engineering.txt"].endswith(b"replacement")
    print(json.dumps({
        "installed_package": openhcs.__file__, "source_path": str(source_path),
        "function_id": key, "scope": contract.execution_scope.value,
        "signature": str(inspect.signature(function)),
        "memory_types": [], "processing_declaration": None,
        "registration": "PASS", "canonical_lookup": "PASS", "listing": "PASS",
        "invalid_abi_no_publication": "PASS", "reload": "PASS", "update_lifetime": "PASS",
        "native_or_pipeline_execution": "NOT RUN",
    }, indent=2))


if __name__ == "__main__":
    main()
