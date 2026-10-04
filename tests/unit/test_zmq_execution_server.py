import sys
from pathlib import Path
from dataclasses import replace
from queue import SimpleQueue
from types import ModuleType, SimpleNamespace

import pytest
from objectstate import get_current_global_config
from zmqruntime.execution import ExecutionServer
from zmqruntime.messages import ExecutionRecord, ExecutionStatus

import openhcs.runtime.zmq_execution_server as zmq_execution_server_module
from openhcs.constants.constants import GroupBy
from openhcs.core.config import (
    GlobalPipelineConfig,
    PipelineConfig,
    ProcessingConfig,
)
from openhcs.core.execution_state import ExecutionOutputPlateSummary
from openhcs.core.orchestrator.execution_result import (
    ExecutionResult,
    RuntimeContextObservation,
    RuntimeExecutionObservation,
    RuntimeObservationMode,
)
from openhcs.core.progress import (
    ProgressEvent,
    ProgressEventPayload,
    ProgressExecutionContext,
    ProgressPhase,
    ProgressStatus,
    create_event,
)
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionOutcomeExport,
)
from openhcs.runtime.zmq_execution_server import (
    ZMQAuxiliaryExecutionParams,
    ZMQExecutionContext,
    ZMQExecutionServer,
)
from openhcs.runtime.zmq_execution_signature import (
    OpenHCSExecutionConfigBundle,
    ZMQExecutionCompileControl,
    ZMQExecutionConfigTransport,
    ZMQExecutionIdentity,
    ZMQExecutionRequestPayload,
    ZMQRuntimeObservationExportScope,
)


def test_zmq_execution_context_seeds_saved_global_config_for_compilation() -> None:
    global_config = GlobalPipelineConfig(
        processing_config=ProcessingConfig(group_by=GroupBy.CHANNEL)
    )
    configs = OpenHCSExecutionConfigBundle(
        global_pipeline=global_config,
        plate_pipeline=PipelineConfig(),
    )
    context = ZMQExecutionContext(
        execution_id="exec-1",
        request_payload=ZMQExecutionRequestPayload(
            identity=ZMQExecutionIdentity(plate_id="/tmp/plate"),
            pipeline_code=(
                "from openhcs.core.config import PipelineConfig\n"
                "pipeline_config = PipelineConfig()\n"
                "pipeline_steps = []\n"
            ),
            config_transport=ZMQExecutionConfigTransport(),
            compile_control=ZMQExecutionCompileControl(),
        ),
        pipeline_steps=[],
        configs=configs,
    )

    assert type(context.pipeline_steps) is list
    assert context.configs is configs
    assert "execution_pipeline" not in dir(context)
    assert "pipeline_steps_boundary" not in dir(context)
    assert "config_carrier" not in dir(context)

    ZMQExecutionServer._ensure_request_global_config_context(context)

    saved_global_config = get_current_global_config(
        GlobalPipelineConfig,
        use_live=False,
    )
    assert saved_global_config is global_config
    assert saved_global_config.processing_config.group_by is GroupBy.CHANNEL


@pytest.mark.parametrize(
    ("compiled_mode", "export_path", "expected_mode"),
    (
        (RuntimeObservationMode.OMIT, None, RuntimeObservationMode.OMIT),
        (
            RuntimeObservationMode.OMIT,
            "/tmp/runtime-observation.pkl",
            RuntimeObservationMode.MERGE_INTO_PARENT,
        ),
        (
            RuntimeObservationMode.MERGE_PLATE_INPUTS,
            None,
            RuntimeObservationMode.MERGE_PLATE_INPUTS,
        ),
        (
            RuntimeObservationMode.MERGE_PLATE_INPUTS,
            "/tmp/runtime-observation.pkl",
            RuntimeObservationMode.MERGE_INTO_PARENT,
        ),
        (
            RuntimeObservationMode.MERGE_INTO_PARENT,
            None,
            RuntimeObservationMode.MERGE_INTO_PARENT,
        ),
    ),
)
def test_zmq_auxiliary_params_strengthen_compiled_observation_requirement(
    compiled_mode,
    export_path,
    expected_mode,
) -> None:
    params = ZMQAuxiliaryExecutionParams.from_transport(
        {"runtime_observation_export_path": export_path}
        if export_path is not None
        else None
    )
    execution_bundle = SimpleNamespace(
        requires_parent_runtime_observation=compiled_mode.collects_records,
        requires_full_parent_runtime_observation=(
            compiled_mode is RuntimeObservationMode.MERGE_INTO_PARENT
        ),
    )

    assert params.runtime_observation_mode_for(execution_bundle) is expected_mode


def test_outcome_export_does_not_strengthen_worker_runtime_value_retention() -> None:
    params = ZMQAuxiliaryExecutionParams(
        runtime_observation_export_path=Path("/tmp/outcomes.pkl.gz"),
        runtime_observation_export_scope=ZMQRuntimeObservationExportScope.OUTCOMES,
    )
    execution_bundle = SimpleNamespace(
        requires_parent_runtime_observation=False,
        requires_full_parent_runtime_observation=False,
    )

    assert (
        params.runtime_observation_mode_for(execution_bundle)
        is RuntimeObservationMode.OMIT
    )
    assert ZMQAuxiliaryExecutionParams.from_transport(params.to_transport()) == params


def test_outcome_export_requires_a_path() -> None:
    with pytest.raises(ValueError, match="requires an export path"):
        ZMQAuxiliaryExecutionParams(
            runtime_observation_export_scope=ZMQRuntimeObservationExportScope.OUTCOMES
        )


def test_server_exports_outcomes_without_projecting_compiled_values(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    server = object.__new__(ZMQExecutionServer)
    server._server_environment = None
    record = ExecutionRecord(
        execution_id="execution-1",
        plate_id="plate-1",
        client_address=None,
        status=ExecutionStatus.RUNNING.value,
    )
    server.active_executions = {record.execution_id: record}
    export_path = tmp_path / "outcomes.pkl.gz"
    request_context = SimpleNamespace(
        execution_id=record.execution_id,
        auxiliary_params=ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=export_path,
            runtime_observation_export_scope=ZMQRuntimeObservationExportScope.OUTCOMES,
        ),
    )
    compilation = SimpleNamespace(
        execution_bundle=SimpleNamespace(
            runtime_contexts={},
            requires_parent_runtime_observation=False,
        ),
        output_plate=SimpleNamespace(output_plate_root=tmp_path),
    )
    monkeypatch.setattr(
        "openhcs.core.runtime_execution_validation.runtime_output_roots",
        lambda contexts, root: (root,),
    )

    declared_output = tmp_path / "exports" / "Saved.tiff"
    declared_output.parent.mkdir()
    declared_output.write_bytes(b"image evidence")
    server._export_runtime_observation(
        request_context=request_context,
        compilation=compilation,
        execution_results={
            "A01": ExecutionResult.success(
                "A01",
                runtime_observation=RuntimeExecutionObservation(
                    contexts=(
                        RuntimeContextObservation(
                            "context",
                            (),
                            runtime_export_paths=(declared_output,),
                        ),
                    )
                ),
            )
        },
    )

    export = ZMQRuntimeExecutionOutcomeExport.read(export_path)
    assert export.successful_axis_count == 1
    assert export.execution_id == record.execution_id
    assert export.exports is not None
    assert export.exports.output_files == (declared_output,)
    assert record.get_extra("runtime_observation_export_path") == str(export_path)
    assert record.get_extra("runtime_observation_export_scope") == "outcomes"


@pytest.mark.parametrize("changed", (None, "pipeline", "config", "plate"))
def test_zmq_server_admits_compiled_declaration_without_reevaluating_source(
    monkeypatch,
    changed,
) -> None:
    import openhcs.processing.func_registry as func_registry_module

    monkeypatch.setattr(
        func_registry_module,
        "initialize_registry",
        lambda: pytest.fail("Direct-import pipeline initialized the full registry"),
    )
    monkeypatch.setattr(
        ZMQExecutionServer,
        "_cleanup_compiled_artifacts",
        lambda self: None,
    )
    monkeypatch.setattr(
        ZMQExecutionServer,
        "_execute_with_orchestrator",
        lambda self, context: context,
    )
    server = ZMQExecutionServer()
    request_payload = ZMQExecutionRequestPayload(
        identity=ZMQExecutionIdentity(plate_id="/tmp/plate"),
        pipeline_code=(
            "from openhcs.core.config import PipelineConfig\n"
            "pipeline_config = PipelineConfig()\n"
            "pipeline_steps = []\n"
        ),
        config_transport=ZMQExecutionConfigTransport(
            config_code=(
                "from openhcs.core.config import GlobalPipelineConfig\n"
                "config = GlobalPipelineConfig()\n"
            ),
        ),
        compile_control=ZMQExecutionCompileControl(compile_artifact_id="compile-1"),
    )

    from openhcs.core.compiled_execution import (
        CompiledExecutionBundle,
        CompiledRuntimeEnvironmentPlan,
    )
    from openhcs.runtime.zmq_compilation import (
        ZMQCompileArtifactRecord,
        ZMQCompilationResult,
    )

    configs = OpenHCSExecutionConfigBundle(GlobalPipelineConfig(), PipelineConfig())
    bundle = CompiledExecutionBundle(
        pipeline_definition=[],
        runtime_contexts={},
        transport_contexts={},
        worker_assignments={},
        runtime_environment=CompiledRuntimeEnvironmentPlan.from_global_config(
            configs.global_pipeline,
            compiled_contexts={},
            server_mode=True,
        ),
    )
    server._compiled_artifacts["compile-1"] = ZMQCompileArtifactRecord(
        execution_id="compile-1",
        plate_id=request_payload.plate_id,
        compilation_signature=request_payload.compilation_signature,
        debug_replay_signature=request_payload.debug_replay_signature,
        compilation=ZMQCompilationResult(bundle, []),
        configs=configs,
    )
    monkeypatch.setattr(
        server,
        "_resolve_request_config",
        lambda *args: pytest.fail("Artifact executed config source"),
    )
    monkeypatch.setattr(
        zmq_execution_server_module.PipelineDocumentAuthority,
        "from_namespace",
        lambda *args: pytest.fail("Artifact rebuilt pipeline declaration"),
    )
    if changed == "pipeline":
        request_payload = replace(
            request_payload,
            pipeline_code=request_payload.pipeline_code
            + "\nraise AssertionError('must not execute')\n",
        )
    elif changed == "config":
        request_payload = replace(
            request_payload,
            config_transport=replace(
                request_payload.config_transport,
                config_code="raise AssertionError('must not execute')",
            ),
        )
    elif changed == "plate":
        request_payload = replace(
            request_payload,
            identity=replace(request_payload.identity, plate_id="/different/source"),
        )
    if changed is not None:
        with pytest.raises(ValueError, match="does not match execution request"):
            server._execute_pipeline("exec-1", request_payload)
        assert "compile-1" in server._compiled_artifacts
        return
    context = server._execute_pipeline("exec-1", request_payload)
    assert context.execution_id == "exec-1"
    assert context.configs is configs
    assert type(context.pipeline_steps) is list
    assert context.pipeline_steps == []
    assert isinstance(context.configs, OpenHCSExecutionConfigBundle)
    assert isinstance(context.configs.global_pipeline, GlobalPipelineConfig)
    assert isinstance(context.pipeline_config, PipelineConfig)
    assert context.compile_artifact_id == "compile-1"


def test_zmq_server_prepares_virtual_import_before_evaluating_pipeline(
    monkeypatch,
) -> None:
    import openhcs
    import openhcs.processing.func_registry as func_registry_module

    initialized: list[str] = []

    def initialize_registry() -> None:
        initialized.append("registry")
        package = ModuleType("openhcs.codex_virtual")
        package.__path__ = []
        module = ModuleType("openhcs.codex_virtual.filters")
        module.noop = lambda value: value
        package.filters = module
        monkeypatch.setitem(sys.modules, package.__name__, package)
        monkeypatch.setitem(sys.modules, module.__name__, module)
        monkeypatch.setattr(openhcs, "codex_virtual", package, raising=False)

    monkeypatch.setattr(
        func_registry_module, "initialize_registry", initialize_registry
    )
    monkeypatch.setattr(
        ZMQExecutionServer, "_cleanup_compiled_artifacts", lambda self: None
    )
    monkeypatch.setattr(
        ZMQExecutionServer,
        "_execute_with_orchestrator",
        lambda self, context: context,
    )
    request_payload = ZMQExecutionRequestPayload(
        identity=ZMQExecutionIdentity(plate_id="/tmp/plate"),
        pipeline_code=(
            "from openhcs.codex_virtual.filters import noop\n"
            "from openhcs.core.config import PipelineConfig\n"
            "pipeline_config = PipelineConfig()\n"
            "pipeline_steps = []\n"
        ),
        config_transport=ZMQExecutionConfigTransport(
            config_code=(
                "from openhcs.core.config import GlobalPipelineConfig\n"
                "config = GlobalPipelineConfig()\n"
            ),
        ),
        compile_control=ZMQExecutionCompileControl(),
    )

    context = ZMQExecutionServer()._execute_pipeline("exec-1", request_payload)

    assert initialized == ["registry"]
    assert context.pipeline_steps == []


def test_zmq_server_forwards_parent_execution_progress_without_worker_claim() -> None:
    server = object.__new__(ZMQExecutionServer)
    server._worker_assignments_by_execution = {
        "execution-1": {"worker_0": ["A01", "B01"]}
    }
    server.progress_queue = SimpleQueue()
    worker_queue = SimpleQueue()
    progress_context = ProgressExecutionContext(
        execution_id="execution-1",
        plate_id="plate-1",
    )
    worker_queue.put(
        create_event(
            ProgressEventPayload(
                identity=progress_context.identity_for_event(
                    axis_id="",
                    step_name="ExportToDatabase",
                ),
                phase=ProgressPhase.RUNNING,
                status=ProgressStatus.RUNNING,
                completed=32,
                total=33,
                percent=(32 / 33) * 100.0,
            )
        ).to_dict()
    )
    worker_queue.put(None)

    server._forward_worker_progress(worker_queue)

    event = ProgressEvent.from_dict(server.progress_queue.get())
    assert event.axis_id == ""
    assert event.worker_slot is None
    assert event.owned_wells is None
    assert event.worker_assignments == {"worker_0": ["A01", "B01"]}
    assert event.total_wells == ["A01", "B01"]


def test_zmq_server_records_the_compilation_output_plate_value_without_rebuilding_it() -> (
    None
):
    server = object.__new__(ZMQExecutionServer)
    server._worker_assignments_by_execution = {}
    record = ExecutionRecord(
        execution_id="execution-1",
        plate_id="plate-1",
        client_address=None,
        status=ExecutionStatus.QUEUED.value,
    )
    server.active_executions = {record.execution_id: record}
    output_plate = ExecutionOutputPlateSummary(
        output_plate_root="/tmp/output",
        auto_add_output_plate_to_plate_manager=True,
    )
    compilation = SimpleNamespace(
        worker_assignments={"worker_0": ["A01"]},
        output_plate=output_plate,
    )

    server._record_compilation_outputs(record.execution_id, compilation)

    assert record.metadata == {
        ExecutionOutputPlateSummary.EXECUTION_RECORD_KEY: output_plate
    }
    assert (
        record.get_extra(ExecutionOutputPlateSummary.EXECUTION_RECORD_KEY)
        is output_plate
    )


def test_zmq_server_stop_releases_process_resources_when_transport_stop_fails(
    monkeypatch,
) -> None:
    server = object.__new__(ZMQExecutionServer)
    events: list[object] = []
    server._function_catalog_preparation = SimpleNamespace(
        cancel_and_join=lambda: events.append("catalog")
    )

    def fail_transport_stop(_server) -> None:
        events.append("transport")
        raise RuntimeError("transport stop failed")

    monkeypatch.setattr(ExecutionServer, "stop", fail_transport_stop)
    monkeypatch.setattr(
        zmq_execution_server_module,
        "cleanup_backend_connections",
        lambda *, include_process_resources: events.append(
            ("process_resources", include_process_resources)
        ),
    )

    with pytest.raises(RuntimeError, match="transport stop failed"):
        server.stop()

    assert events == ["transport", "catalog", ("process_resources", True)]


def test_compiled_source_adoption_owns_fresh_runtime_services_and_live_source_gate(
    tmp_path,
):
    import json
    from polystore.base import reset_memory_backend
    from polystore.virtual_workspace import VirtualWorkspaceBackend
    from openhcs.constants.constants import Backend
    from openhcs.core.compiled_execution import (
        CompiledExecutionBundle,
        CompiledRuntimeEnvironmentPlan,
    )
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.orchestrator.cancellation import ExecutionCancelledError
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.microscopes.openhcs import OpenHCSMicroscopeHandler

    previous = PipelineOrchestrator(
        plate_path=tmp_path, pipeline_config=PipelineConfig()
    )
    metadata_path = tmp_path / "polystore_metadata.json"
    metadata_path.write_text(
        json.dumps(
            {
                "subdirectories": {
                    "images": {
                        "workspace_mapping": {
                            "image.tif": {
                                "backend": Backend.MEMORY.value,
                                "backend_address": str(tmp_path / "source.tif"),
                                "source_axis_indices": [],
                            }
                        },
                    }
                }
            }
        )
    )
    virtual_workspace = VirtualWorkspaceBackend(plate_root=tmp_path)
    previous.filemanager.register_backend(
        Backend.VIRTUAL_WORKSPACE.value, virtual_workspace
    )
    previous._execution_cancellation.request()
    previous.filemanager.ensure_directory(str(tmp_path), Backend.MEMORY.value)
    previous.filemanager.save("stale", str(tmp_path / "old.tif"), Backend.MEMORY.value)
    handler = OpenHCSMicroscopeHandler(previous.filemanager)
    context = ProcessingContext(axis_id="A01", filemanager=previous.filemanager)
    context.plate_path = tmp_path
    context.input_dir = tmp_path
    context.microscope_handler = handler
    transport = ProcessingContext(axis_id="A01")
    bundle = CompiledExecutionBundle(
        pipeline_definition=[],
        runtime_contexts={"A01": context},
        transport_contexts={"A01": transport},
        worker_assignments={},
        runtime_environment=CompiledRuntimeEnvironmentPlan.from_global_config(
            GlobalPipelineConfig(),
            compiled_contexts={"A01": context},
            server_mode=True,
        ),
    )
    reset_memory_backend()
    runtime = PipelineOrchestrator(
        plate_path=tmp_path, pipeline_config=PipelineConfig()
    )
    runtime.execution_id = "next-execution"
    runtime.adopt_compiled_execution(bundle)
    assert runtime.filemanager is not previous.filemanager
    assert (
        runtime.filemanager.registry[Backend.VIRTUAL_WORKSPACE.value]
        is virtual_workspace
    )
    assert not runtime.filemanager.exists(
        str(tmp_path / "old.tif"), Backend.MEMORY.value
    )
    assert not context.filemanager.exists(
        str(tmp_path / "old.tif"), Backend.MEMORY.value
    )
    runtime.filemanager.save("live", str(tmp_path / "source.tif"), Backend.MEMORY.value)
    assert (
        runtime.filemanager.load(
            str(tmp_path / "image.tif"),
            Backend.VIRTUAL_WORKSPACE.value,
        )
        == "live"
    )
    assert bundle.runtime_contexts["A01"] is context
    assert bundle.transport_contexts["A01"] is transport
    assert runtime.microscope_handler is handler
    assert runtime.execution_id == "next-execution"
    signal = runtime._execution_cancellation.begin()
    signal.raise_if_requested("new execution")
    runtime._execution_cancellation.request()
    with pytest.raises(ExecutionCancelledError):
        signal.raise_if_requested("active execution")
    runtime._execution_cancellation.finish(signal)
    metadata_path.unlink()
    tmp_path.rmdir()
    unavailable = PipelineOrchestrator(
        plate_path=tmp_path, pipeline_config=PipelineConfig()
    )
    with pytest.raises(FileNotFoundError):
        unavailable.adopt_compiled_execution(bundle)
    assert not unavailable.is_initialized()
