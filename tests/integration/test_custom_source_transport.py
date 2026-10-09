"""Synthetic stdpickle and spawned-worker transport, without UI or science data.

The producer persists through CustomFunctionManager. An independently started
consumer has only those durable sources and the pickle, never producer globals.
No assertion depends on a helper's eventual module name or pickle wire format.
"""

from __future__ import annotations

import dataclasses
import os
import pickle
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import pytest

WORKTREE = Path(__file__).resolve().parents[2]
PYTHON = Path(sys.executable)
NAMES = ("transport_synthetic_alpha", "transport_synthetic_beta")
TOKENS = ("alpha_units", "beta_units")
OUTPUT_LIMIT = 16_384

# Apply explicit source backing before spawn unpickles its product initializer,
# not only in the producer's __main__ path. Ordinary installed runs omit this.
dependency_root = os.environ.get("OPENHCS_SOURCE_VALIDATION_EXTERNAL_ROOT")
if dependency_root:
    sys.path.insert(0, str(WORKTREE))
    from openhcs._source_dependencies import ensure_source_checkout_external_paths
    ensure_source_checkout_external_paths(Path(dependency_root))


@pytest.fixture(autouse=True)
def cleanup_test_runtime_resources():
    """Override the global viewer cleanup: this file owns no live resources."""
    yield


@pytest.fixture
def transport_environment(tmp_path):
    env = os.environ.copy()
    for key in ("DATA", "CONFIG", "CACHE", "STATE", "RUNTIME"):
        directory = tmp_path / key.lower()
        directory.mkdir(mode=0o700)
        env[f"XDG_{key}_HOME" if key != "RUNTIME" else "XDG_RUNTIME_DIR"] = str(
            directory
        )
    env.update(
        PYTHONPATH=str(WORKTREE),
        PYTHONDONTWRITEBYTECODE="1",
        OPENHCS_CPU_ONLY="true",
        OPENHCS_HEADLESS="true",
        OPENHCS_SUBPROCESS_NO_GPU="1",
        QT_QPA_PLATFORM="offscreen",
        CUDA_VISIBLE_DEVICES="",
        PYTEST_DISABLE_PLUGIN_AUTOLOAD="1",
        NUMBA_CACHE_DIR=str(tmp_path / "numba"),
        MPLCONFIGDIR=str(tmp_path / "matplotlib"),
        OMP_NUM_THREADS="1",
        OPENBLAS_NUM_THREADS="1",
    )
    return env


def _run_child(env, *arguments):
    """Bound each interpreter to 30 seconds and combined output to 16 KiB."""
    command = [str(PYTHON), "-B", str(Path(__file__).resolve()), *arguments]
    captured = bytearray()
    deadline = time.monotonic() + 30
    with (
        tempfile.TemporaryFile(mode="w+b") as output_file,
        subprocess.Popen(
            command,
            cwd=WORKTREE,
            env=env,
            stdout=output_file,
            stderr=subprocess.STDOUT,
        ) as process,
    ):
        try:
            while True:
                remaining = deadline - time.monotonic()
                assert remaining > 0, f"Child exceeded 30s: {arguments!r}"
                assert os.fstat(output_file.fileno()).st_size < OUTPUT_LIMIT, (
                    f"Child output exceeded {OUTPUT_LIMIT} bytes: {arguments!r}"
                )
                try:
                    returncode = process.wait(timeout=min(remaining, 0.1))
                except subprocess.TimeoutExpired:
                    continue
                break
            output_file.seek(0)
            captured.extend(output_file.read(OUTPUT_LIMIT))
            assert len(captured) < OUTPUT_LIMIT, (
                f"Child output exceeded {OUTPUT_LIMIT} bytes: {arguments!r}"
            )
        finally:
            if process.poll() is None:
                process.kill()
                process.wait(timeout=1)
    output = captured.decode("utf-8", errors="replace")
    assert returncode == 0, f"Child {arguments!r} exited {returncode}:\n{output}"
    assert "transport-ok" in output, output
    return output


def _source(name, token):
    # These two capabilities are unrelated, not a chain of feature-owner bases.
    # Both sources deliberately declare exactly the same helper class names.
    return f"""
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory import numpy
from openhcs.core.artifacts import (
    ArtifactSpec, ArtifactViewerStreaming, GroupLineageSourceRelation,
    ImageArtifactType, MainFlowPlaneProjectionOutputSpec, MeasurementsArtifactType,
    ObjectLabelsArtifactType, ObjectMeasurementSubjectRelation,
)
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
from openhcs.core.runtime_measurements import (
    ObjectMeasurementValueRow, RuntimeMeasurementFeature, RuntimeMeasurementFeatureOwner,
)

class HelperFeature(RuntimeMeasurementFeature):
    VALUE = {token!r}

class HelperUnit(str, Enum):
    UNIT = {token!r}

@dataclass(frozen=True)
class HelperRow(ObjectMeasurementValueRow):
    unit: HelperUnit = HelperUnit.UNIT

class RowCapability:
    row_type = HelperRow
    feature_type = HelperFeature

    @classmethod
    def make_row(cls, value):
        return cls.row_type(7, cls.feature_type.VALUE.value, value)

class UnitCapability:
    unit_type = HelperUnit

    @classmethod
    def unit_label(cls):
        return cls.unit_type.UNIT.value

class HelperFeatureOwner(RowCapability, UnitCapability, RuntimeMeasurementFeatureOwner):
    capability_types = (RowCapability, UnitCapability)

    @classmethod
    def owns_measurement_feature_name(cls, feature_name):
        return feature_name in tuple(feature.value for feature in cls.feature_type)

    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name):
        return cls.owns_measurement_feature_name(feature_name)

input_spec = ArtifactSpec.input(
    "SyntheticInput", ObjectLabelsArtifactType, parameter_name="auxiliary", required=False,
)
measurement_spec = ArtifactSpec.output(
    "SyntheticMeasurements", MeasurementsArtifactType, required=False,
    viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
    measurement_feature_owner=HelperFeatureOwner,
    relations=(GroupLineageSourceRelation(input_spec.ref()),
               ObjectMeasurementSubjectRelation(input_spec.ref())),
)
image_spec = MainFlowPlaneProjectionOutputSpec.output(
    "SyntheticProjection", ImageArtifactType,
    relations=(GroupLineageSourceRelation(input_spec.ref()),),
)

@numpy
@artifact_inputs(input_spec)
@artifact_outputs(measurement_spec, image_spec)
def {name}(image, auxiliary=None):
    return image
"""


def _manager():
    from openhcs.core.xdg_paths import get_openhcs_data_dir
    from openhcs.processing.custom_functions import CustomFunctionManager

    # Preexistence prevents get_data_file_path's legacy-home migration entirely.
    isolated_data = get_openhcs_data_dir()
    assert isolated_data.is_relative_to(Path(os.environ["XDG_DATA_HOME"]))
    (isolated_data / "custom_functions").mkdir(exist_ok=True)
    manager = CustomFunctionManager()
    assert manager.storage_dir.is_relative_to(isolated_data)
    return manager


def _inspection(func):
    from openhcs.core.artifact_inspection import CompiledArtifactInvocationInspection
    from openhcs.core.artifacts import ArtifactOutputPlan
    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.function_patterns import (
        CompiledFunctionInvocation,
        FunctionInvocationKey,
        InvocationArtifactInputEdgePlan,
        InvocationArtifactInputProjectionKey,
    )

    contract = CallableContract.from_callable(func)
    key = FunctionInvocationKey(contract.function_name, "synthetic_group", 2)
    plans = tuple(
        ArtifactOutputPlan(
            name=spec.name,
            artifact_type=spec.artifact_type,
            path=f"/synthetic-only/{contract.function_name}/{spec.name}.pkl",
            materialization=spec.materialization,
            viewer_streaming=spec.viewer_streaming,
            relations=spec.relations,
            sidecar_role=spec.sidecar_role,
            producer_step_index=3,
            producer_step_scope_id="synthetic_scope",
            producer_step_name="Synthetic producer",
        )
        for spec in contract.artifact_outputs
    )
    edges = tuple(
        InvocationArtifactInputEdgePlan(
            key=InvocationArtifactInputProjectionKey(key, index),
            spec=spec,
            storage_plan=None,
            projection=None,
        )
        for index, spec in enumerate(contract.artifact_inputs)
    )
    return CompiledArtifactInvocationInspection.from_invocation(
        CompiledFunctionInvocation(
            key=key,
            contract=contract,
            artifact_input_edges=edges,
            artifact_output_plans=plans,
        )
    )


def _helper_values(owner):
    return (
        owner.feature_type,
        owner.feature_type.VALUE,
        owner.unit_type,
        owner.unit_type.UNIT,
        owner.row_type,
        owner.make_row(2.5),
        owner.capability_types,
    )


def _assert_specs(actual, expected):
    assert actual == tuple(expected)
    for transported, declared in zip(actual, expected, strict=True):
        assert type(transported) is type(declared)
        # ArtifactSpec equality deliberately ignores this operational field.
        assert transported.parameter_name == declared.parameter_name
        assert (
            transported.measurement_feature_owner is declared.measurement_feature_owner
        )


def _assert_payload(payload, kind):
    from openhcs.core.artifact_inspection import CompiledArtifactInvocationInspection
    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.function_reference import FunctionReferenceTransportAuthority
    from openhcs.core.runtime_measurements import ObjectMeasurementValueRow
    from openhcs.processing import custom_functions

    owners = []
    for name, token, (value, helpers) in zip(NAMES, TOKENS, payload, strict=True):
        authoritative = getattr(custom_functions, name)
        contract = CallableContract.from_callable(authoritative)
        owner = contract.artifact_outputs[0].measurement_feature_owner
        if kind == "inspection":
            assert type(value) is CompiledArtifactInvocationInspection
            expected = _inspection(authoritative)
            assert value == expected
            _assert_specs(value.output_specs, contract.artifact_outputs)
            _assert_specs(
                tuple(edge.spec for edge in value.input_edges), contract.artifact_inputs
            )
            # Edge equality also ignores storage_plan; check it explicitly.
            assert tuple(edge.storage_plan for edge in value.input_edges) == (None,)
            assert value.output_plans == expected.output_plans
        else:
            expected = FunctionReferenceTransportAuthority.function_reference(
                authoritative
            )
            assert type(value) is type(expected)
            assert value == expected
            _assert_specs(value.metadata.artifact_outputs, contract.artifact_outputs)
            _assert_specs(value.metadata.artifact_inputs, contract.artifact_inputs)
            assert value.metadata.artifact_input_parameter_names == ("auxiliary",)
            resolved = value.resolve()
            assert value.resolve() is resolved  # Exercise the warm reference cache.
            resolved_owner = (
                CallableContract.from_callable(resolved)
                .artifact_outputs[0]
                .measurement_feature_owner
            )
            assert resolved_owner is owner
        feature_type, feature, unit_type, unit, row_type, row, capabilities = helpers
        assert feature_type is owner.feature_type
        assert feature is owner.feature_type.VALUE
        assert unit_type is owner.unit_type
        assert unit is owner.unit_type.UNIT
        assert row_type is owner.row_type
        assert type(row) is owner.row_type
        assert issubclass(row_type, ObjectMeasurementValueRow)
        assert dataclasses.is_dataclass(row_type)
        assert row == owner.make_row(2.5)
        assert row.object_label == 7 and row.result_value == 2.5
        assert row.feature_name == token and row.unit is unit
        assert feature.value == token and owner.unit_label() == token
        assert owner.owns_measurement_feature_name(token)
        assert owner.owns_primary_measurement_feature_name(token)
        assert not owner.owns_measurement_feature_name("unrelated")
        assert capabilities == owner.capability_types
        rows, units = capabilities
        assert rows is owner.capability_types[0]
        assert units is owner.capability_types[1]
        assert not issubclass(rows, units) and not issubclass(units, rows)
        assert issubclass(owner, rows) and issubclass(owner, units)
        assert rows in owner.__mro__ and units in owner.__mro__
        assert rows.make_row(2.5) == row and units.unit_label() == token
        owners.append(owner)
    first, second = owners
    assert first is not second
    assert first.feature_type is not second.feature_type
    assert first.unit_type is not second.unit_type
    assert first.row_type is not second.row_type
    assert all(
        a is not b
        for a, b in zip(first.capability_types, second.capability_types, strict=True)
    )
    assert not first.owns_measurement_feature_name(TOKENS[1])
    assert not second.owns_measurement_feature_name(TOKENS[0])


def _produce(path, kind):
    from openhcs.core.callable_contract import CallableContract
    from openhcs.core.function_reference import FunctionReferenceTransportAuthority

    manager = _manager()
    payload = []
    for name, token in zip(NAMES, TOKENS, strict=True):
        (func,) = manager.register_from_code(
            _source(name, token), persist=True, clear_caches=False, emit_signal=False
        )
        assert manager.get_function_code(name) == _source(name, token)
        value = (
            _inspection(func)
            if kind == "inspection"
            else FunctionReferenceTransportAuthority.function_reference(func)
        )
        owner = (
            CallableContract.from_callable(func)
            .artifact_outputs[0]
            .measurement_feature_owner
        )
        payload.append((value, _helper_values(owner)))
    payload = tuple(payload)
    _assert_payload(payload, kind)
    print(f"stdpickle producer: {kind}", flush=True)
    with path.open("wb") as stream:
        pickle.dump(payload, stream, protocol=pickle.HIGHEST_PROTOCOL)


def _load(path):
    with path.open("rb") as stream:
        return pickle.load(stream)


def _mutate(mutation):
    manager = _manager()
    if mutation == "deleted":
        assert manager.delete_custom_function(NAMES[0])
    else:
        name = NAMES[0] if mutation == "changed" else "transport_synthetic_renamed"
        assert (
            manager.update_custom_function(NAMES[0], _source(name, "changed_units"))
            == name
        )


def _require_stale_rejection(operation):
    # Unpickling may reject an absent/revised source before resolve can run.
    # Do not select that implementation detail, an exception message, or a codec.
    try:
        operation()
    except (RuntimeError, AttributeError, ImportError):
        return
    raise AssertionError("A persisted reference accepted a stale source revision")


def _spawned_custom_task(payload, execution_id, plate_id):
    """Run actual registered declarations and emit through the initialized queue."""
    import numpy as np
    from openhcs.core.progress import emit, ProgressPhase, ProgressStatus

    _assert_payload(payload, "reference")
    values = np.arange(6, dtype=np.uint16).reshape(2, 3)
    results = []
    for reference, _helpers in payload:
        np.testing.assert_array_equal(reference.resolve()(values), values)
        owner = reference.metadata.artifact_outputs[0].measurement_feature_owner
        results.append(owner.make_row(2.5))
    emit(execution_id=execution_id, plate_id=plate_id, axis_id="synthetic",
         step_name="custom", phase=ProgressPhase.STEP_COMPLETED,
         status=ProgressStatus.SUCCESS, percent=100)
    return os.getpid(), tuple(results)


def _spawned_compiled_custom_task(context, helpers):
    """Exercise queue transport of the captured contract, not just its reference."""
    import numpy as np
    from openhcs.core.function_reference import FunctionReference

    plan = context.step_plans[0]
    (invocation,) = tuple(plan.compiled_function_pattern.iter_invocations())
    assert isinstance(invocation.contract.raw_processing_function, FunctionReference)
    assert invocation.contract.metadata.prepare is None
    values = np.arange(6, dtype=np.uint16).reshape(2, 3)
    np.testing.assert_array_equal(invocation.runtime_callable(values), values)
    owner = invocation.contract.artifact_outputs[0].measurement_feature_owner
    assert owner.row_type is helpers[4]
    assert owner.make_row(2.5) == helpers[5]
    return context.axis_id, os.getpid(), values.tolist(), owner.make_row(2.5)


def _compiled_custom_contexts(payload, runtime):
    from polystore.filemanager import FileManager
    from polystore.memory import MemoryStorageBackend
    from openhcs.constants.constants import Backend
    from openhcs.core.compiled_execution import CompiledExecutionBundle
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.function_patterns import (
        compile_function_pattern, normalize_function_pattern,
    )
    from openhcs.core.function_step_transport import FunctionStepTransportAuthority

    contexts = {}
    for index, (reference, _helpers) in enumerate(payload):
        axis_id = f"synthetic_{index}"
        # Compilation captures metadata from the registered runtime callable.
        # Unlike an already-referenced pattern, this carries a displaced raw
        # callable until the existing transport projection derives its owner.
        captured = normalize_function_pattern(reference.resolve())
        pattern = compile_function_pattern(captured, {}, {})
        (invocation,) = tuple(pattern.iter_invocations())
        assert callable(invocation.contract.raw_processing_function)
        prepared = invocation.contract.resolve_runtime_callable()
        plan = CompiledStepPlan(
            step_index=0, step_name="Synthetic custom", step_type="FunctionStep",
            axis_id=axis_id, compiled_function_pattern=pattern,
        )
        context = ProcessingContext(
            axis_id=axis_id, step_plans={0: plan},
            filemanager=FileManager({Backend.MEMORY.value: MemoryStorageBackend()}),
        )
        context.freeze()
        contexts[axis_id] = context
        normalized = FunctionStepTransportAuthority.normalize_context(context)
        transported = next(
            normalized.step_plans[0].compiled_function_pattern.iter_invocations()
        )
        assert transported.contract is not invocation.contract
        assert invocation.contract.resolve_runtime_callable() is prepared
        assert callable(invocation.contract.raw_processing_function)
        assert FunctionStepTransportAuthority.normalize_callable_contract(
            transported.contract
        ) is transported.contract
    return CompiledExecutionBundle.from_runtime_contexts(
        pipeline_definition=(), runtime_contexts=contexts,
        worker_assignments={f"worker_{i}": [axis] for i, axis in enumerate(contexts)},
        runtime_environment=runtime,
    ).transport_contexts


def _spawn(path):
    import multiprocessing
    from openhcs.core.compiled_execution import (
        CompiledRuntimeEnvironmentPlan, CompiledWorkerStartPlan,
    )
    from openhcs.core.config import MultiprocessingStartMethod
    from openhcs.core.orchestrator.cancellation import ExecutionCancellationSignal
    from openhcs.core.orchestrator.worker_execution import WorkerExecutorFactory
    from openhcs.core.progress import ProgressExecutionContext

    # A future derived context can carry nontransportable local runtime state;
    # no generic worker-bootstrap consumer should need to learn its fields.
    @dataclasses.dataclass(frozen=True)
    class RichProgressContext(ProgressExecutionContext):
        runtime_callback: object

    context = RichProgressContext("spawn-custom", "synthetic-plate", lambda: None)
    _produce(path, "reference")
    payload = _load(path)
    method = MultiprocessingStartMethod.SPAWN
    runtime = CompiledRuntimeEnvironmentPlan(
        worker_start=CompiledWorkerStartPlan(method, method, "source fixture", False, False),
        use_threading=False, configured_num_workers=2,
    )
    queue = multiprocessing.get_context(method.value).Queue()
    resources = WorkerExecutorFactory(
        log_file_base=None, progress_queue=queue,
        cancellation=ExecutionCancellationSignal(),
    ).create(runtime_environment=runtime, actual_max_workers=2)
    contexts = _compiled_custom_contexts(payload, runtime)
    try:
        with resources.execution_context():
            tasks = tuple(
                resources.executor.submit(_spawned_compiled_custom_task, lane_context, helpers)
                for lane_context, (_reference, helpers) in zip(
                    contexts.values(), payload, strict=True
                )
            )
            for (axis, lane_context), task, (_reference, helpers) in zip(
                contexts.items(), tasks, payload, strict=True
            ):
                observed_axis, worker_pid, values, row = task.result(timeout=15)
                assert observed_axis == axis and lane_context.axis_id == axis
                assert worker_pid != os.getpid()
                assert values == [[0, 1, 2], [3, 4, 5]]
                assert type(row) is helpers[4] and row == helpers[5]
            pid, rows = resources.executor.submit(
                _spawned_custom_task, payload, context.execution_id, context.plate_id,
            ).result(timeout=15)
        assert pid != os.getpid()
        for row, (_reference, helpers) in zip(rows, payload, strict=True):
            assert type(row) is helpers[4]
            assert row == helpers[5]
        progress = queue.get(timeout=5)
        assert progress["execution_id"] == context.execution_id
        assert progress["plate_id"] == context.plate_id
        assert progress["pid"] == pid
        assert progress["status"] == "success"
        assert progress["percent"] == 100
        print(f"spawned custom revision/progress/rows: worker {pid}", flush=True)
    finally:
        queue.close()
        queue.join_thread()


def _child_main():
    # A script's sys.path starts in tests/integration, not the worktree root.
    sys.path.insert(0, str(WORKTREE))
    import openhcs
    from openhcs.processing.custom_functions import manager as manager_module
    from openhcs.processing.custom_functions import runtime_registry

    assert Path(openhcs.__file__).resolve() == WORKTREE / "openhcs/__init__.py"
    assert Path(manager_module.__file__).resolve().is_relative_to(WORKTREE)
    assert Path(runtime_registry.__file__).resolve().is_relative_to(WORKTREE)
    assert Path(sys.executable) == PYTHON
    print(f"provenance: {sys.executable}; {openhcs.__file__}", flush=True)
    _manager()
    assert not runtime_registry.CustomFunctionRuntimeRegistry.metadata_by_name()
    role, raw_path, kind, state, mutation = sys.argv[1:]
    path = Path(raw_path)
    if role == "produce":
        _produce(path, kind)
    elif role == "spawn":
        _spawn(path)
    elif role == "mutate":
        _mutate(mutation)
    elif role == "consume":
        if state == "warm":
            # Reverse producer order to expose helper-name/global collisions.
            for name in reversed(NAMES):
                _manager().load_custom_function(name)
        payload = _load(path)
        _assert_payload(payload, kind)
        if mutation != "unchanged":
            old_reference = payload[0][0]
            assert old_reference.resolve() is old_reference.resolve()
            _mutate(mutation)
            _require_stale_rejection(old_reference.resolve)
            _require_stale_rejection(lambda: _load(path)[0][0].resolve())
            # Alpha's lifecycle must leave beta's nominal helper identity intact.
            from openhcs.core.callable_contract import CallableContract

            beta = CallableContract.from_callable(payload[1][0].resolve())
            beta_owner = beta.artifact_outputs[0].measurement_feature_owner
            assert beta_owner.feature_type is payload[1][1][0]
            assert beta_owner.unit_label() == TOKENS[1]
    elif role == "reject":
        _require_stale_rejection(lambda: _load(path)[0][0].resolve())
        # A change to alpha must not prevent beta's independent source loading.
        from openhcs.core.callable_contract import CallableContract
        from openhcs.processing import custom_functions

        beta = CallableContract.from_callable(getattr(custom_functions, NAMES[1]))
        assert (
            beta.artifact_outputs[0].measurement_feature_owner.unit_label() == TOKENS[1]
        )
    else:
        raise AssertionError(role)
    print("transport-ok", flush=True)


@pytest.mark.parametrize("kind", ["inspection", "reference"])
@pytest.mark.parametrize("state", ["cold", "warm"])
def test_persisted_payload_preserves_nominal_helpers_in_independent_consumer(
    tmp_path, transport_environment, kind, state
):
    path = tmp_path / "transport.pkl"
    _run_child(transport_environment, "produce", str(path), kind, state, "unchanged")
    _run_child(transport_environment, "consume", str(path), kind, state, "unchanged")


def test_persisted_custom_revision_executes_in_original_spawn_factory(
    tmp_path, transport_environment,
):
    print(_run_child(transport_environment, "spawn", str(tmp_path / "spawn.pkl"),
                     "reference", "cold", "unchanged"), end="")


@pytest.mark.parametrize("mutation", ["changed", "deleted", "renamed"])
@pytest.mark.parametrize("state", ["cold", "warm"])
def test_persisted_reference_rejects_stale_source_revision(
    tmp_path, transport_environment, mutation, state
):
    path = tmp_path / "transport.pkl"
    _run_child(
        transport_environment, "produce", str(path), "reference", state, "unchanged"
    )
    if state == "cold":
        # Positive fresh-process control prevents unrelated unpickle errors from
        # being mistaken for rejection. The mutator is yet another interpreter.
        _run_child(
            transport_environment, "consume", str(path), "reference", state, "unchanged"
        )
        _run_child(
            transport_environment, "mutate", str(path), "reference", state, mutation
        )
        _run_child(
            transport_environment, "reject", str(path), "reference", state, mutation
        )
    else:
        _run_child(
            transport_environment, "consume", str(path), "reference", state, mutation
        )


if __name__ == "__main__":
    _child_main()
