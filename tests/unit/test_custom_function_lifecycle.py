"""Transaction and concurrency boundaries for persisted custom functions."""

from __future__ import annotations

import concurrent.futures
import inspect
import pickle
import threading
from types import SimpleNamespace

import numpy as np
import pytest
from arraybridge import MemoryType

import openhcs.processing.custom_functions as custom_functions
import openhcs.processing.custom_functions.manager as manager_module
from openhcs.core.function_reference import FunctionReferenceTransportAuthority
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionRuntimeRegistry,
)
from openhcs.processing.custom_functions.templates import AVAILABLE_MEMORY_TYPES
from openhcs.processing.custom_functions.validation import ValidationError


def _source(name: str, expression: str = "image") -> str:
    return f"@numpy\ndef {name}(image):\n    return {expression}\n"


def _plate_source(name: str) -> str:
    return f'''from openhcs.core.artifacts import ArtifactSpec, SpecialArtifactType
from openhcs.core.callable_contract import FunctionStepExecutionScope
from openhcs.core.pipeline.function_contracts import (
    artifact_outputs, execution_scope, runtime_bound_parameters,
)
from openhcs.core.runtime_stores import RuntimeArtifactBatch

@execution_scope(FunctionStepExecutionScope.PLATE)
@runtime_bound_parameters(RuntimeArtifactBatch)
@artifact_outputs(ArtifactSpec.output("EngineeringBundle", SpecialArtifactType))
def {name}(*, artifact_batch: RuntimeArtifactBatch):
    return {{"engineering.txt": b"independent ABI fixture"}}
'''


@pytest.mark.parametrize("persist", (True, False))
def test_custom_plate_uses_native_abi_projection_and_source_lifecycle(
    isolated_custom_runtime, persist,
) -> None:
    from openhcs.core.callable_contract import CallableContract, FunctionStepExecutionScope
    from openhcs.core.pipeline.funcstep_contract_validator import FuncStepContractValidator
    from openhcs.processing.custom_functions.runtime_registry import CustomFunctionMetadata
    from openhcs.processing.func_registry import get_function

    source = _plate_source("engineering_plate_probe")
    manager = CustomFunctionManager()
    [function] = manager.register_from_code(source, persist=persist)
    metadata = CustomFunctionRuntimeRegistry.metadata_by_name()["engineering_plate_probe"]
    assert isinstance(metadata, CustomFunctionMetadata)
    assert get_function(metadata.composite_key) is function
    contract = CallableContract.from_callable(function)
    assert contract.execution_scope is FunctionStepExecutionScope.PLATE
    assert not contract.declared_memory_types
    assert contract.processing_contract is None
    assert metadata.tags == ["openhcs", "custom"]
    FuncStepContractValidator.validate_plate_callable_contracts((contract,), "engineering")
    reference = FunctionReferenceTransportAuthority.function_reference(function)
    assert reference.resolve() is function

    if persist:
        assert manager.source_path_for_function(function).read_text() == source
        [info] = manager.list_custom_functions()
        assert info.name == "engineering_plate_probe"
        assert info.memory_type is None
        assert info.backend_label == "plate"
        CustomFunctionRuntimeRegistry.clear()
        assert manager.load_all_custom_functions() == 1
        reloaded = get_function(metadata.composite_key)
        assert CallableContract.from_callable(reloaded).processing_contract is None
        manager.update_custom_function("engineering_plate_probe", source.replace("fixture", "replacement"))
        with pytest.raises(RuntimeError, match="changed"):
            reference.resolve()
    else:
        assert not tuple(isolated_custom_runtime.glob("*.py"))


@pytest.mark.parametrize(
    "replacement",
    (
        "artifact_batch: int",
        "artifact_batch: RuntimeArtifactBatch = None",
        "artifact_batch: RuntimeArtifactBatch",
    ),
)
def test_custom_plate_rejects_invalid_original_batch_abi_without_publication(
    isolated_custom_runtime, replacement,
) -> None:
    source = _plate_source("engineering_invalid_plate_probe")
    source = source.replace("*, artifact_batch: RuntimeArtifactBatch", replacement)
    with pytest.raises(ValidationError):
        CustomFunctionManager().register_from_code(source)
    assert not tuple(isolated_custom_runtime.glob("*.py"))
    assert CustomFunctionRuntimeRegistry.metadata_by_name() == {}
    assert "engineering_invalid_plate_probe" not in vars(custom_functions)


def test_custom_plate_does_not_admit_axis_memory_contract(
    isolated_custom_runtime,
) -> None:
    source = _plate_source("engineering_mixed_scope_probe").replace(
        "@execution_scope", "@numpy\n@execution_scope",
    )
    with pytest.raises(ValidationError, match="cannot declare axis-local"):
        CustomFunctionManager().register_from_code(source)
    assert not tuple(isolated_custom_runtime.glob("*.py"))
    assert CustomFunctionRuntimeRegistry.metadata_by_name() == {}


def _measurement_source(name: str) -> str:
    return f"""from dataclasses import dataclass
from openhcs.core.artifacts import (
    ArtifactSpec, MainFlowStackOutputSpec, ImageArtifactType, MeasurementsArtifactType,
)
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.runtime_measurements import (
    RuntimeMeasurementFeature, RuntimeMeasurementFeatureOwner,
)

class ProbeFeature(RuntimeMeasurementFeature):
    COUNT = "count"

class ProbeFeatureOwner(RuntimeMeasurementFeatureOwner):
    @classmethod
    def owns_measurement_feature_name(cls, feature_name):
        return any(feature.feature_name == feature_name for feature in ProbeFeature)

    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name):
        return cls.owns_measurement_feature_name(feature_name)

@dataclass(frozen=True)
class ProbeRow:
    count: int

@numpy
@artifact_outputs(
    MainFlowStackOutputSpec.output("ProbeImage", ImageArtifactType),
    ArtifactSpec.output(
        "ProbeRows", MeasurementsArtifactType,
        measurement_feature_owner=ProbeFeatureOwner,
    ),
)
def {name}(image):
    return image, DataclassMeasurementColumnarRows((ProbeRow(1),), row_type=ProbeRow)
"""


def test_compiled_inspection_preserves_custom_helper_identity_and_source_isolation(
    isolated_custom_runtime,
) -> None:
    from openhcs.core.artifact_inspection import CompiledArtifactInvocationInspection
    from openhcs.core.artifacts import ArtifactOutputPlan
    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.function_patterns import (
        DEFAULT_GROUP_KEY,
        CompiledFunctionInvocation,
        FunctionInvocationKey,
    )

    manager = CustomFunctionManager()
    inspections = []
    owners = []
    for name in ("helper_identity_first", "helper_identity_second"):
        [function] = manager.register_from_code(_measurement_source(name))
        contract = CallableContract.from_callable(function)
        _image_spec, spec = contract.artifact_outputs
        owners.append(spec.measurement_feature_owner)
        inspections.append(
            CompiledArtifactInvocationInspection.from_invocation(
                CompiledFunctionInvocation(
                    key=FunctionInvocationKey(name, DEFAULT_GROUP_KEY, 0),
                    contract=contract,
                    artifact_output_plans=tuple(
                        ArtifactOutputPlan(
                            name=output.name,
                            path=f"/memory/{name}/{output.name}.pkl",
                            artifact_type=output.artifact_type,
                            relations=output.relations,
                        )
                        for output in contract.artifact_outputs
                    ),
                )
            )
        )

    assert owners[0] is not owners[1]
    restored = pickle.loads(pickle.dumps(tuple(inspections)))
    for original, received, owner in zip(inspections, restored, owners, strict=True):
        assert received == original
        assert received.output_specs[1].measurement_feature_owner is owner
        assert owner.owns_primary_measurement_feature_name("count")
        assert not owner.owns_measurement_feature_name("unknown")


@pytest.mark.parametrize("operation", ("reconcile", "unchanged-update"))
def test_unchanged_source_lifecycle_preserves_measurement_owner(
    isolated_custom_runtime,
    monkeypatch,
    operation,
) -> None:
    from openhcs.core.callable_contract import CallableContract

    manager = CustomFunctionManager()
    [registered] = manager.register_from_code(_measurement_source("helper_reconcile"))
    _image_spec, before = CallableContract.from_callable(registered).artifact_outputs

    def reject_reexecution(self, code):
        raise AssertionError("Unchanged published source must not execute again")

    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", reject_reexecution)

    if operation == "reconcile":
        assert manager.load_all_custom_functions() == 1
    else:
        assert (
            manager.update_custom_function(
                "helper_reconcile", _measurement_source("helper_reconcile")
            )
            == "helper_reconcile"
        )
    reconciled = CustomFunctionRuntimeRegistry.metadata_by_name()[
        "helper_reconcile"
    ].func
    _image_spec, after = CallableContract.from_callable(reconciled).artifact_outputs
    assert reconciled is registered
    assert after.measurement_feature_owner is before.measurement_feature_owner
    assert manager.load_all_custom_functions() == 1


def test_reconciliation_replaces_helper_owner_only_when_source_changes(
    isolated_custom_runtime,
) -> None:
    from openhcs.core.callable_contract import CallableContract

    manager = CustomFunctionManager()
    name = "helper_source_change"
    code = _measurement_source(name)
    [registered] = manager.register_from_code(code)
    _image_spec, before = CallableContract.from_callable(registered).artifact_outputs
    (isolated_custom_runtime / f"{name}.py").write_text(
        code.replace('COUNT = "count"', 'SIZE = "size"').replace(
            "count: int", "size: int"
        ),
        encoding="utf-8",
    )

    assert manager.load_all_custom_functions() == 1
    reconciled = CustomFunctionRuntimeRegistry.metadata_by_name()[name].func
    _image_spec, after = CallableContract.from_callable(reconciled).artifact_outputs
    assert reconciled is not registered
    assert after.measurement_feature_owner is not before.measurement_feature_owner
    assert after.measurement_feature_owner.owns_measurement_feature_name("size")
    assert not after.measurement_feature_owner.owns_measurement_feature_name("count")


@pytest.mark.parametrize("operation", ("reconcile", "unchanged-update", "reload"))
def test_publication_preserves_owner_recreated_while_prepared_source_waits(
    isolated_custom_runtime,
    monkeypatch,
    operation,
) -> None:
    from openhcs.core.callable_contract import CallableContract

    manager = CustomFunctionManager()
    name = "recreated_source_publication_probe"
    code = _measurement_source(name)
    [original] = manager.register_from_code(code)
    selected = threading.Event()
    release = threading.Event()
    prepare = CustomFunctionRuntimeRegistry.prepare_source_once

    def wait_after_selection(cls, source, factory):
        metadata = prepare(source, factory)
        selected.set()
        assert release.wait(timeout=5)
        return metadata

    monkeypatch.setattr(
        CustomFunctionRuntimeRegistry,
        "prepare_source_once",
        classmethod(wait_after_selection),
    )

    def pending_publication():
        if operation == "reconcile":
            return manager.load_all_custom_functions()
        if operation == "unchanged-update":
            return manager.update_custom_function(name, code)
        return manager.load_custom_function(name)

    with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
        future = executor.submit(pending_publication)
        try:
            assert selected.wait(timeout=5)
            assert manager.delete_custom_function(name)
            [current] = manager.register_from_code(code)
            assert current is not original
            owner = (
                CallableContract.from_callable(current)
                .artifact_outputs[1]
                .measurement_feature_owner
            )
            payload = pickle.dumps(owner)
        finally:
            release.set()
        assert future.result(timeout=5) == (
            name if operation == "unchanged-update" else 1
        )

    assert vars(custom_functions)[name] is current
    assert CustomFunctionRuntimeRegistry.metadata_by_name()[name].func is current
    assert (
        CallableContract.from_callable(current)
        .artifact_outputs[1]
        .measurement_feature_owner
        is owner
    )
    assert pickle.loads(payload) is owner


@pytest.mark.parametrize("operation", ("recreate", "replace", "delete"))
def test_pending_resolution_rejects_retired_source_without_poisoning_current_owner(
    isolated_custom_runtime,
    monkeypatch,
    operation,
) -> None:
    from openhcs.core.callable_contract import CallableContract
    from openhcs.processing.backends.lib_registry.openhcs_registry import (
        OpenHCSRegistry,
    )

    monkeypatch.setattr(RegistryService, "_metadata_cache", None)
    monkeypatch.setattr(RegistryService, "_resolved_reference_callables", {})
    manager = CustomFunctionManager()
    name = "pending_resolution_source_probe"
    code = _measurement_source(name)
    [original] = manager.register_from_code(code)
    reference = FunctionReferenceTransportAuthority.function_reference(original)
    selected = threading.Event()
    release = threading.Event()
    reconstruct = OpenHCSRegistry.reconstruct_cached_callable

    def pause_reconstruction(self, declared, contract):
        result = reconstruct(self, declared, contract)
        if declared is original:
            selected.set()
            assert release.wait(timeout=5)
        return result

    monkeypatch.setattr(
        OpenHCSRegistry,
        "reconstruct_cached_callable",
        pause_reconstruction,
    )
    with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
        future = executor.submit(reference.resolve)
        try:
            assert selected.wait(timeout=5)
            if operation == "replace":
                manager.update_custom_function(
                    name, code.replace("ProbeRow(1)", "ProbeRow(2)")
                )
                current = vars(custom_functions)[name]
            else:
                assert manager.delete_custom_function(name)
                if operation == "recreate":
                    [current] = manager.register_from_code(code)
                else:
                    current = None
        finally:
            release.set()
        with pytest.raises(RuntimeError, match="changed"):
            future.result(timeout=5)

    if current is None:
        with pytest.raises(RuntimeError):
            reference.resolve()
    else:
        fresh = FunctionReferenceTransportAuthority.function_reference(current)
        resolved = fresh.resolve()
        expected = CallableContract.from_callable(current).artifact_outputs[1]
        actual = CallableContract.from_callable(resolved).artifact_outputs[1]
        assert actual.measurement_feature_owner is expected.measurement_feature_owner
        assert resolved is fresh.resolve()


@pytest.fixture
def isolated_custom_runtime(monkeypatch, tmp_path):
    storage_dir = tmp_path / "custom_functions"
    storage_dir.mkdir()
    monkeypatch.setattr(manager_module, "get_data_file_path", lambda _name, *, create=True: storage_dir)
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_declarations_by_name", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_published_exports", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_preparation_outcomes", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_preparation_threads", {})
    monkeypatch.setattr(CustomFunctionRuntimeRegistry, "_source_revision", None)
    yield storage_dir
    CustomFunctionRuntimeRegistry.clear()


@pytest.mark.parametrize("persist", (False, True))
def test_registration_observation_uses_current_owners_without_loading(
    isolated_custom_runtime, monkeypatch, persist,
):
    from dataclasses import replace
    from openhcs.agent.dto.functions import (
        CustomFunctionRegistrationHandle, CustomFunctionRegistrationRequest,
        CustomFunctionRegistrationObservationOutcome,
    )
    from openhcs.agent.path_policy import AgentPathPolicy
    from openhcs.agent.services.function_catalog_service import FunctionCatalogService
    from zmqruntime.messages import ProcessIdentity

    root = isolated_custom_runtime
    policy = AgentPathPolicy.with_roots(readable_roots=(root,), writable_roots=(root,))
    manager = CustomFunctionManager(create_storage=False)
    request = CustomFunctionRegistrationRequest.from_fields(
        source_code=_source("observation_probe"), function_name="observation_probe",
        persist=persist, storage_dir=str(root), port=22319,
    )
    handle = CustomFunctionRegistrationHandle.from_request(replace(request, server_identity=ProcessIdentity.current()))
    service = FunctionCatalogService(path_policy=policy)
    before = service.observe_custom_function_registration(handle)
    assert before.outcome is CustomFunctionRegistrationObservationOutcome.NOT_OBSERVED
    [function] = manager.register_from_code(request.source_code, persist=persist, clear_caches=False, emit_signal=False)
    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", lambda *_: pytest.fail("Read-only observation cannot evaluate source"))
    monkeypatch.setattr(CustomFunctionManager, "load_custom_function", lambda *_a, **_k: pytest.fail("Read-only observation cannot lazy load"))
    observed = service.observe_custom_function_registration(handle)
    assert observed.outcome is CustomFunctionRegistrationObservationOutcome.REGISTERED
    assert observed.published_sources == (handle.require_named_source(),)
    assert CustomFunctionRuntimeRegistry.metadata_by_name()["observation_probe"].func is function
    assert observed.persisted_source == (handle.require_named_source() if persist else None)
    changed = service.observe_custom_function_registration(replace(handle, content_sha256="0" * 64))
    assert changed.outcome is CustomFunctionRegistrationObservationOutcome.NOT_OBSERVED
    assert not changed.published_sources
    with pytest.raises(RuntimeError, match="stale"):
        service.observe_custom_function_registration(replace(handle, server_identity=replace(ProcessIdentity.current(), create_time=0)))
    CustomFunctionRuntimeRegistry.remove("observation_probe")
    after = service.observe_custom_function_registration(handle)
    assert after.outcome is (CustomFunctionRegistrationObservationOutcome.PERSISTED_ONLY if persist else CustomFunctionRegistrationObservationOutcome.NOT_OBSERVED)


def test_register_rejects_multi_declaration_source_without_partial_publication(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()

    with pytest.raises(ValidationError, match="exactly one"):
        manager.register_from_code(
            _source("first_probe") + "\n" + _source("second_probe"),
        )

    assert CustomFunctionRuntimeRegistry.metadata_by_name() == {}
    assert not tuple(isolated_custom_runtime.glob("*.py"))
    assert "first_probe" not in vars(custom_functions)


@pytest.mark.parametrize(
    "decorator",
    [
        "numpy",
        "numpy(contract=ProcessingContract.PURE_2D)",
        "cpu(contract=ProcessingContract.PURE_2D)",
        "decorators.numpy(contract=ProcessingContract.PURE_2D)",
    ],
)
def test_custom_registration_uses_callable_contract_not_decorator_spelling(
    isolated_custom_runtime,
    decorator,
) -> None:
    from openhcs.core.callable_contract import CallableContract
    from openhcs.processing.backends.lib_registry.unified_registry import (
        ProcessingContract,
    )

    source = (
        "from openhcs.core.memory.decorators import numpy as cpu\n"
        "from openhcs.core.memory import decorators\n"
        "from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract\n"
        f"@{decorator}\ndef contract_probe(image):\n    return image + 1\n"
    )
    [function] = CustomFunctionManager().register_from_code(source)
    contract = CallableContract.from_callable(function)
    assert contract.input_memory_type == MemoryType.NUMPY.value
    assert contract.output_memory_type == MemoryType.NUMPY.value
    if "contract=" in decorator:
        assert contract.declared_processing_contract == ProcessingContract.PURE_2D.name
    assert np.array_equal(function(np.asarray([[3]])), [[4]])
    assert (isolated_custom_runtime / "contract_probe.py").read_text() == source


@pytest.mark.parametrize(
    "source",
    [
        "def undecorated_probe(image):\n    return image\n",
        "def numpy(function):\n    return function\n@numpy\ndef fake_probe(image):\n    return image\n",
        "from openhcs.core.memory.decorators import numpy\nclass Container:\n    def numpy(image):\n        return image\n",
        "@numpy\nasync def async_probe(image):\n    return image\n",
    ],
)
def test_custom_registration_rejects_missing_real_declaration_without_publication(
    isolated_custom_runtime,
    source,
) -> None:
    with pytest.raises(ValidationError, match="exactly one decorated"):
        CustomFunctionManager().register_from_code(source)
    assert CustomFunctionRuntimeRegistry.metadata_by_name() == {}
    assert not tuple(isolated_custom_runtime.glob("*.py"))


def test_invalid_update_preserves_file_and_runtime_identity(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()
    [original] = manager.register_from_code(_source("stable_probe"))
    source_path = isolated_custom_runtime / "stable_probe.py"
    original_source = source_path.read_text(encoding="utf-8")

    with pytest.raises(ValidationError):
        manager.update_custom_function(
            "stable_probe",
            "@numpy\ndef broken_probe(value):\n    return value\n",
        )

    assert source_path.read_text(encoding="utf-8") == original_source
    assert vars(custom_functions)["stable_probe"] is original
    assert (
        CustomFunctionRuntimeRegistry.metadata_by_name()["stable_probe"].func
        is original
    )


def test_rename_reconciles_file_runtime_and_public_export(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()
    manager.register_from_code(_source("old_probe"))

    new_name = manager.update_custom_function(
        "old_probe", _source("new_probe", "image + 1")
    )

    assert new_name == "new_probe"
    assert not (isolated_custom_runtime / "old_probe.py").exists()
    assert (isolated_custom_runtime / "new_probe.py").exists()
    assert "old_probe" not in vars(custom_functions)
    assert "old_probe" not in CustomFunctionRuntimeRegistry.metadata_by_name()
    assert np.array_equal(vars(custom_functions)["new_probe"](np.asarray([[1]])), [[2]])


def test_rename_rejects_existing_runtime_target_without_mutation(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()
    [old_callable] = manager.register_from_code(_source("old_probe"))
    [target_callable] = manager.register_from_code(
        _source("target_probe"), persist=False
    )
    old_source = (isolated_custom_runtime / "old_probe.py").read_text(encoding="utf-8")

    with pytest.raises(ValueError, match="already exists"):
        manager.update_custom_function("old_probe", _source("target_probe"))

    assert (isolated_custom_runtime / "old_probe.py").read_text(
        encoding="utf-8"
    ) == old_source
    assert vars(custom_functions)["old_probe"] is old_callable
    assert vars(custom_functions)["target_probe"] is target_callable


def test_failed_bulk_reconciliation_preserves_last_proven_projection(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()
    (isolated_custom_runtime / "stable_probe.py").write_text(
        _source("stable_probe"), encoding="utf-8"
    )
    assert manager.load_all_custom_functions() == 1
    prior_revision = CustomFunctionRuntimeRegistry.source_revision()
    prior_callable = vars(custom_functions)["stable_probe"]
    (isolated_custom_runtime / "broken_probe.py").write_text(
        "@numpy\ndef broken_probe(value):\n    return value\n",
        encoding="utf-8",
    )

    with pytest.raises(ValidationError):
        manager.load_all_custom_functions()

    assert CustomFunctionRuntimeRegistry.source_revision() == prior_revision
    assert vars(custom_functions)["stable_probe"] is prior_callable
    assert "broken_probe" not in CustomFunctionRuntimeRegistry.metadata_by_name()

    (isolated_custom_runtime / "broken_probe.py").write_text(
        _source("broken_probe"), encoding="utf-8"
    )
    assert manager.load_all_custom_functions() == 2
    assert CustomFunctionRuntimeRegistry.source_revision() == manager.source_revision()


def test_concurrent_lazy_imports_publish_one_callable_identity(
    isolated_custom_runtime,
) -> None:
    function_name = "concurrent_probe"
    (isolated_custom_runtime / f"{function_name}.py").write_text(
        _source(function_name), encoding="utf-8"
    )
    vars(custom_functions).pop(function_name, None)
    start = threading.Barrier(12)

    def import_one():
        start.wait(timeout=5)
        return getattr(custom_functions, function_name)

    with concurrent.futures.ThreadPoolExecutor(max_workers=12) as executor:
        callables = tuple(executor.map(lambda _index: import_one(), range(12)))

    assert len({id(func) for func in callables}) == 1
    assert vars(custom_functions)[function_name] is callables[0]


def test_concurrent_failed_loads_share_one_exact_source_outcome(
    isolated_custom_runtime,
    monkeypatch,
) -> None:
    function_name = "concurrent_failure_probe"
    (isolated_custom_runtime / f"{function_name}.py").write_text(
        _source(function_name), encoding="utf-8"
    )
    prepare_calls = 0
    prepare_lock = threading.Lock()

    def failing_prepare(self, code):
        del self, code
        nonlocal prepare_calls
        with prepare_lock:
            prepare_calls += 1
        raise ValidationError("shared source failure")

    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", failing_prepare)
    start = threading.Barrier(8)

    def load_one():
        start.wait(timeout=5)
        return CustomFunctionManager().load_custom_function(function_name)

    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as executor:
        futures = tuple(executor.submit(load_one) for _index in range(8))
        for future in futures:
            with pytest.raises(ValidationError, match="shared source failure"):
                future.result(timeout=5)

    assert prepare_calls == 1
    assert function_name not in CustomFunctionRuntimeRegistry.metadata_by_name()


def test_delete_linearizes_after_inflight_lazy_load(
    isolated_custom_runtime,
    monkeypatch,
) -> None:
    function_name = "delete_race_probe"
    (isolated_custom_runtime / f"{function_name}.py").write_text(
        _source(function_name), encoding="utf-8"
    )
    vars(custom_functions).pop(function_name, None)
    entered = threading.Event()
    release = threading.Event()
    original_prepare = CustomFunctionManager._prepare_source

    def blocking_prepare(self, code):
        entered.set()
        assert release.wait(timeout=5)
        return original_prepare(self, code)

    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", blocking_prepare)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        load_future = executor.submit(getattr, custom_functions, function_name)
        assert entered.wait(timeout=5)
        delete_future = executor.submit(
            CustomFunctionManager().delete_custom_function, function_name
        )
        assert delete_future.result(timeout=5)
        release.set()
        with pytest.raises(ValidationError, match="changed during preparation"):
            load_future.result(timeout=5)

    assert not (isolated_custom_runtime / f"{function_name}.py").exists()
    assert function_name not in vars(custom_functions)
    assert function_name not in CustomFunctionRuntimeRegistry.metadata_by_name()


def test_bulk_reconciliation_rejects_revision_drift_before_publication(
    isolated_custom_runtime,
    monkeypatch,
) -> None:
    function_name = "revision_race_probe"
    source_path = isolated_custom_runtime / f"{function_name}.py"
    source_path.write_text(
        _source(function_name, "image + 1"),
        encoding="utf-8",
    )
    entered = threading.Event()
    release = threading.Event()
    original_prepare = CustomFunctionManager._prepare_source

    def blocking_prepare(self, code):
        entered.set()
        assert release.wait(timeout=5)
        return original_prepare(self, code)

    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", blocking_prepare)
    with concurrent.futures.ThreadPoolExecutor(max_workers=1) as executor:
        load_future = executor.submit(CustomFunctionManager().load_all_custom_functions)
        assert entered.wait(timeout=5)
        source_path.write_text(
            _source(function_name, "image + 2"),
            encoding="utf-8",
        )
        release.set()
        with pytest.raises(ValidationError, match="changed during preparation"):
            load_future.result(timeout=5)

    assert CustomFunctionRuntimeRegistry.metadata_by_name() == {}
    assert CustomFunctionRuntimeRegistry.source_revision() is None
    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", original_prepare)
    assert CustomFunctionManager().load_all_custom_functions() == 1
    assert np.array_equal(
        vars(custom_functions)[function_name](np.asarray([[1]])),
        [[3]],
    )


def test_source_preparation_does_not_hold_lifecycle_lock(
    isolated_custom_runtime,
    monkeypatch,
) -> None:
    function_name = "reentrant_prepare_probe"
    source_path = isolated_custom_runtime / f"{function_name}.py"
    source_path.write_text(_source(function_name), encoding="utf-8")
    original_prepare = CustomFunctionManager._prepare_source
    worker_threads = []
    delete_completed_during_prepare = []

    def reentrant_prepare(self, code):
        worker = threading.Thread(
            target=CustomFunctionManager().delete_custom_function,
            args=(function_name,),
        )
        worker_threads.append(worker)
        worker.start()
        worker.join(timeout=1)
        delete_completed_during_prepare.append(not worker.is_alive())
        return original_prepare(self, code)

    monkeypatch.setattr(CustomFunctionManager, "_prepare_source", reentrant_prepare)
    with pytest.raises(ValidationError, match="changed during preparation"):
        CustomFunctionManager().load_custom_function(function_name)
    for worker in worker_threads:
        worker.join(timeout=5)

    assert delete_completed_during_prepare == [True]
    assert not source_path.exists()
    assert function_name not in CustomFunctionRuntimeRegistry.metadata_by_name()


def test_public_package_api_name_collision_preserves_original_owner(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()
    original_manager_class = vars(custom_functions)["CustomFunctionManager"]

    with pytest.raises(ValueError, match="public package export"):
        manager.register_from_code(
            _source("CustomFunctionManager"),
        )

    assert vars(custom_functions)["CustomFunctionManager"] is original_manager_class
    assert (
        "CustomFunctionManager" not in CustomFunctionRuntimeRegistry.metadata_by_name()
    )
    assert not (isolated_custom_runtime / "CustomFunctionManager.py").exists()


def test_removal_preserves_export_that_displaced_published_callable(
    isolated_custom_runtime,
) -> None:
    function_name = "displaced_export_probe"
    manager = CustomFunctionManager()
    manager.register_from_code(_source(function_name))
    replacement_owner = object()
    setattr(custom_functions, function_name, replacement_owner)

    assert manager.delete_custom_function(function_name)

    assert vars(custom_functions)[function_name] is replacement_owner
    assert function_name not in CustomFunctionRuntimeRegistry.metadata_by_name()
    vars(custom_functions).pop(function_name)


def test_cold_registration_never_prepares_global_catalog(
    isolated_custom_runtime,
    monkeypatch,
) -> None:
    monkeypatch.setattr(RegistryService, "_metadata_cache", None)
    monkeypatch.setattr(
        RegistryService,
        "get_all_functions_with_metadata",
        classmethod(
            lambda cls, **kwargs: pytest.fail("cold registration prepared catalog")
        ),
    )

    [registered] = CustomFunctionManager().register_from_code(
        _source("cold_probe"), persist=False
    )

    assert registered is vars(custom_functions)["cold_probe"]


def test_persisted_source_reconciliation_retains_ephemeral_declarations(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()
    [ephemeral] = manager.register_from_code(
        _source("ephemeral_probe"),
        persist=False,
    )
    manager.register_from_code(_source("persisted_probe"), persist=True)

    assert manager.load_all_custom_functions() == 1

    metadata = CustomFunctionRuntimeRegistry.metadata_by_name()
    assert metadata["ephemeral_probe"].func is ephemeral
    assert "persisted_probe" in metadata
    assert vars(custom_functions)["ephemeral_probe"] is ephemeral


def test_custom_function_framework_surfaces_derive_from_memory_type_owner(
    isolated_custom_runtime,
) -> None:
    manager = CustomFunctionManager()
    declared_names = tuple(memory_type.value for memory_type in MemoryType)

    assert AVAILABLE_MEMORY_TYPES == declared_names
    assert set(manager._create_execution_namespace()) == {
        "__name__",
        *declared_names,
    }


def test_source_helper_is_not_misidentified_as_processing_declaration(
    isolated_custom_runtime,
) -> None:
    source = (
        "def helper(image):\n"
        "    return image + 1\n\n"
        "@numpy\n"
        "def processing_probe(image):\n"
        "    return helper(image)\n"
    )
    source_path = isolated_custom_runtime / "processing_probe.py"
    source_path.write_text(source, encoding="utf-8")

    info = CustomFunctionManager().list_custom_functions()

    assert [(item.name, item.memory_type) for item in info] == [
        ("processing_probe", MemoryType.NUMPY.value)
    ]
    assert CustomFunctionRuntimeRegistry.metadata_by_name() == {}


def test_registration_rejects_name_claim_proven_by_cached_canonical_catalog(
    isolated_custom_runtime,
    monkeypatch,
) -> None:
    monkeypatch.setattr(
        RegistryService,
        "_metadata_cache",
        {
            "openhcs:cellprofiler_crop": SimpleNamespace(
                tags=("openhcs", "cellprofiler")
            )
        },
    )
    monkeypatch.setattr(
        RegistryService,
        "get_all_functions_with_metadata",
        classmethod(
            lambda cls, **kwargs: pytest.fail("collision check prepared catalog")
        ),
    )

    with pytest.raises(ValueError, match="canonical OpenHCS function"):
        CustomFunctionManager().register_from_code(_source("cellprofiler_crop"))

    assert not (isolated_custom_runtime / "cellprofiler_crop.py").exists()
    assert "cellprofiler_crop" not in CustomFunctionRuntimeRegistry.metadata_by_name()


def test_compiled_custom_reference_rejects_changed_source_revision(
    isolated_custom_runtime,
    monkeypatch,
) -> None:
    manager = CustomFunctionManager()
    [original] = manager.register_from_code(_source("revision_contract_probe"))
    reference = FunctionReferenceTransportAuthority.function_reference(original)

    manager.update_custom_function(
        "revision_contract_probe",
        "@cupy\ndef revision_contract_probe(image):\n    return image\n",
    )

    with pytest.raises(RuntimeError, match="changed after this reference was compiled"):
        reference.resolve()

    monkeypatch.setattr(
        RegistryService,
        "get_all_functions_with_metadata",
        classmethod(
            lambda cls, **kwargs: pytest.fail(
                "current custom declaration fell back to global catalog discovery"
            )
        ),
    )
    current = vars(custom_functions)["revision_contract_probe"]
    assert (
        FunctionReferenceTransportAuthority.function_reference(current).resolve()
        is current
    )


@pytest.mark.parametrize("mutation", ("changed", "deleted"))
def test_warm_reference_and_helper_reject_source_edits_outside_manager(
    isolated_custom_runtime,
    mutation,
) -> None:
    manager = CustomFunctionManager()
    name = "outside_manager_revision_probe"
    code = _measurement_source(name)
    [function] = manager.register_from_code(code)
    reference = FunctionReferenceTransportAuthority.function_reference(function)
    assert reference.resolve() is reference.resolve()
    owner = reference.metadata.artifact_outputs[1].measurement_feature_owner
    owner_payload = pickle.dumps(owner)
    assert pickle.loads(owner_payload) is owner

    source_path = isolated_custom_runtime / f"{name}.py"
    if mutation == "changed":
        source_path.write_text(code + "\n# An external editor changed this revision.\n")
    else:
        source_path.unlink()

    with pytest.raises(RuntimeError, match="recompile"):
        reference.resolve()
    with pytest.raises(RuntimeError, match="recompile"):
        pickle.loads(owner_payload)
    # CPython's producer wraps a failed global lookup in PicklingError; the
    # consumer propagates the namespace's actual stale-revision rejection.
    with pytest.raises(pickle.PicklingError):
        pickle.dumps(owner)


@pytest.mark.parametrize("persist", (False, True))
def test_nested_helpers_and_functions_keep_identity_without_imported_type_mutation(
    isolated_custom_runtime,
    persist,
) -> None:
    from pathlib import Path

    code = """from dataclasses import dataclass
from enum import Enum
from pathlib import Path

def helper_value(value):
    return value * 2

class source:
    @dataclass(frozen=True)
    class Row:
        value: int

    class Kind(Enum):
        VALUE = "local"

@numpy
def nested_helper_transport_probe(image):
    return image
"""
    [function] = CustomFunctionManager().register_from_code(code, persist=persist)
    namespace = inspect.unwrap(function).__globals__
    helper = namespace["helper_value"]
    nested = namespace["source"]
    original = (helper, nested, nested.Row, nested.Row(3), nested.Kind.VALUE)
    restored = pickle.loads(pickle.dumps(original))
    assert restored[0] is helper and restored[0](4) == 8
    assert restored[1] is nested
    assert restored[2] is nested.Row and type(restored[3]) is nested.Row
    assert restored[3] == nested.Row(3)
    assert restored[4] is nested.Kind.VALUE
    assert namespace["Path"] is Path
    assert Path.__module__ == "pathlib" and Path.__qualname__ == "Path"
    reference = FunctionReferenceTransportAuthority.function_reference(function)
    assert reference.resolve() is reference.resolve()
    assert (
        isolated_custom_runtime / "nested_helper_transport_probe.py"
    ).exists() is persist

    CustomFunctionRuntimeRegistry.clear()
    with pytest.raises((RuntimeError, pickle.PicklingError)):
        pickle.dumps(helper)


@pytest.mark.parametrize("operation", ["replace", "remove", "reconcile", "clear", "stale_preparation"])
def test_source_retirement_thaws_before_dropping_captured_owners(
    isolated_custom_runtime, monkeypatch, operation,
):
    from openhcs.processing.custom_functions.source_namespace import CustomFunctionSource

    manager = CustomFunctionManager()
    name = "startup_gc_retirement_probe"
    manager.register_from_code(_source(name))
    previous = CustomFunctionRuntimeRegistry.metadata_by_name()[name]
    calls = []
    monkeypatch.setattr(RegistryService, "_startup_heap_frozen", True)

    def unfreeze():
        # All five actual retirement boundaries still own the original export.
        assert vars(custom_functions)[name] is previous.func
        calls.append("thaw")

    monkeypatch.setattr("openhcs.processing.backends.lib_registry.registry_service.gc.unfreeze", unfreeze)
    if operation == "replace":
        manager.update_custom_function(name, _source(name, "image + 1"))
    elif operation == "remove":
        CustomFunctionRuntimeRegistry.remove(name)
    elif operation == "reconcile":
        (isolated_custom_runtime / f"{name}.py").unlink()
        manager.load_all_custom_functions()
    elif operation == "clear":
        CustomFunctionRuntimeRegistry.clear()
    else:
        old = CustomFunctionSource(name, "old-preparation")
        current = CustomFunctionSource(name, "new-preparation")
        outcome = concurrent.futures.Future()
        outcome.set_result(previous)
        CustomFunctionRuntimeRegistry._preparation_outcomes[old] = outcome
        CustomFunctionRuntimeRegistry.prepare_source_once(current, lambda: previous)
    assert calls == ["thaw"]
    assert not RegistryService._startup_heap_frozen
