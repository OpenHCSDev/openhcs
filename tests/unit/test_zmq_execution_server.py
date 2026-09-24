from pathlib import Path
from queue import SimpleQueue
from types import SimpleNamespace

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
        requires_parent_runtime_observation=compiled_mode.collects_records
    )

    assert params.runtime_observation_mode_for(execution_bundle) is expected_mode


def test_outcome_export_does_not_strengthen_worker_runtime_value_retention() -> None:
    params = ZMQAuxiliaryExecutionParams(
        runtime_observation_export_path=Path("/tmp/outcomes.pkl.gz"),
        runtime_observation_export_scope=ZMQRuntimeObservationExportScope.OUTCOMES,
    )
    execution_bundle = SimpleNamespace(requires_parent_runtime_observation=False)

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
        execution_bundle=SimpleNamespace(runtime_contexts={}),
        output_plate=SimpleNamespace(output_plate_root=tmp_path),
    )
    monkeypatch.setattr(
        "openhcs.core.runtime_execution_validation.runtime_output_roots",
        lambda contexts, root: (root,),
    )

    server._export_runtime_observation(
        request_context=request_context,
        compilation=compilation,
        execution_results={"A01": ExecutionResult.success("A01")},
    )

    export = ZMQRuntimeExecutionOutcomeExport.read(export_path)
    assert export.successful_axis_count == 1
    assert export.execution_id == record.execution_id
    assert export.exports is not None
    assert export.exports.output_files == ()
    assert record.get_extra("runtime_observation_export_path") == str(export_path)
    assert record.get_extra("runtime_observation_export_scope") == "outcomes"


def test_zmq_server_reconstructs_pipeline_and_configs_for_artifact_execution(
    monkeypatch,
) -> None:
    import openhcs.processing.func_registry as func_registry_module

    monkeypatch.setattr(func_registry_module, "_registry_initialized", True)
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

    context = server._execute_pipeline("exec-1", request_payload)

    assert type(context.pipeline_steps) is list
    assert context.pipeline_steps == []
    assert isinstance(context.configs, OpenHCSExecutionConfigBundle)
    assert isinstance(context.configs.global_pipeline, GlobalPipelineConfig)
    assert isinstance(context.pipeline_config, PipelineConfig)
    assert context.compile_artifact_id == "compile-1"


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
