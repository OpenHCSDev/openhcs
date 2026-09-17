from __future__ import annotations

import hashlib
from pathlib import Path

from benchmark.agent_validation.challenge_functions import (
    expand_labels_without_overlap,
)
from benchmark.agent_validation.contracts import (
    AttemptPhase,
    DiagnosticCheck,
    DslRequirement,
)
from benchmark.agent_validation.mcp_attempt_recorder import (
    AttemptObservation,
    McpAttemptRecorder,
)
from openhcs.agent.dto.common import RenderedSource
from openhcs.agent.dto.execution import (
    ArtifactPlanInspection,
    CompiledStepPlanSummary,
    ExecutionJobStatus,
    MainFlowMaterializationPlanSummary,
)
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationResult,
    FunctionCatalogEntry,
    FunctionDetail,
)
from openhcs.agent.dto.ui_bridge import (
    UiCodeDocument,
    UiCodeDocumentIdentity,
    UiCodeDocumentSummary,
)
from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.mcp.dev_client import McpDevCommandExecution
from openhcs.serialization.json import to_jsonable


class _FakeMcpClient:
    def __init__(self, executions: tuple[McpDevCommandExecution, ...]) -> None:
        self._executions = iter(executions)

    def execute(self, argv, *, timeout_seconds=None):
        del argv, timeout_seconds
        return next(self._executions)


def _execution(tool: str, payload: object = None, *, returncode: int = 0):
    payload_value = {} if payload is None else to_jsonable(payload)
    response = {
        "server": {"command": "python", "module": "openhcs.mcp"},
        "errors": [],
        "results": [
            {
                "tool": tool,
                "mcp_error": False,
                "payloads": [payload_value],
            }
        ],
    }
    return McpDevCommandExecution(
        argv=(tool,),
        payload=response,
        rendered_output="",
        returncode=returncode,
        server_stderr_tail=None,
    )


def _failed_payload_execution(tool: str):
    return McpDevCommandExecution(
        argv=(tool,),
        payload={
            "server": {"command": "python", "module": "openhcs.mcp"},
            "errors": [],
            "results": [
                {
                    "tool": tool,
                    "mcp_error": False,
                    "payloads": [
                        {
                            "errors": [
                                {
                                    "code": "execution_failed",
                                    "message": "runtime rejected the request",
                                    "hint": None,
                                    "exception_type": "RuntimeError",
                                    "path": None,
                                }
                            ]
                        }
                    ],
                }
            ],
        },
        rendered_output="",
        returncode=0,
        server_stderr_tail=None,
    )


def _pipeline_source() -> str:
    return PipelineDocumentAuthority.render(
        PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(),
            pipeline_steps=[
                FunctionStep(
                    func=[
                        (expand_labels_without_overlap, {"radius": 1}),
                        (expand_labels_without_overlap, {"radius": 1}),
                    ],
                    name="expand labels",
                )
            ],
        )
    )


def _function_entry() -> FunctionCatalogEntry:
    return FunctionCatalogEntry(
        function_id="openhcs:expand_labels_without_overlap",
        import_path=(
            "benchmark.agent_validation.challenge_functions."
            "expand_labels_without_overlap"
        ),
        name="expand_labels_without_overlap",
        module="benchmark.agent_validation.challenge_functions",
        library="openhcs",
        signature="(label_image: ndarray, radius: int = 1) -> ndarray",
        summary="Expand labels without overlap.",
        backend_tags=("numpy",),
    )


def _ui_pipeline_document(source: str) -> UiCodeDocument:
    encoded = source.encode()
    return UiCodeDocument(
        schema_version="openhcs.agent.v1",
        summary=UiCodeDocumentSummary(
            widget_id="pipeline_editor",
            schema_version="openhcs.agent.v1",
            identity=UiCodeDocumentIdentity(document_id="pipeline_editor"),
            title="Pipeline editor",
            readable=True,
            writable=True,
        ),
        source=source,
        mime_type="text/x-python",
        size_bytes=len(encoded),
        sha256=hashlib.sha256(encoded).hexdigest(),
    )


def _completed_job(kind: str, job_id: str) -> ExecutionJobStatus:
    return ExecutionJobStatus(
        schema_version="openhcs.agent.v1",
        session_id="session-1",
        job_id=job_id,
        kind=kind,
        uri=f"openhcs://execution/jobs/{job_id}",
        server_execution_id=f"server-{job_id}",
        status="complete",
    )


def test_attempt_recorder_derives_dsl_evidence_from_mcp_receipts(tmp_path: Path):
    source = _pipeline_source()
    entry = _function_entry()
    executions = (
        _execution(
            "openhcs_register_custom_function",
            CustomFunctionRegistrationResult(
                schema_version="openhcs.agent.v1",
                registered_count=1,
                functions=(entry,),
            ),
        ),
        _execution(
            "openhcs_describe_function",
            FunctionDetail(
                schema_version="openhcs.agent.v1",
                entry=entry,
                parameters=(),
                doc="Expand labels without overlap.",
            ),
        ),
        _execution("openhcs_add_function_step"),
        _execution("openhcs_validate_pipeline"),
        _execution(
            "openhcs_render_pipeline_source",
            RenderedSource(
                schema_version="openhcs.agent.v1",
                title="pipeline",
                source=source,
            ),
        ),
        _execution("openhcs_ui_get_code_document", _ui_pipeline_document(source)),
        _execution("openhcs_ui_apply_code_document"),
        _execution(
            "openhcs_inspect_pipeline_source_artifact_plan",
            ArtifactPlanInspection(
                schema_version="openhcs.agent.v1",
                plate_path="/plate",
                step_count=1,
                steps=(
                    CompiledStepPlanSummary(
                        step_index=0,
                        step_name="expand labels",
                        axis_id="A01",
                        output_dir="/output",
                        main_flow_materialization=MainFlowMaterializationPlanSummary(
                            output_dir="/output/checkpoints",
                            backend="disk",
                            plate_root="/output",
                            sub_dir="checkpoints",
                        ),
                    ),
                ),
            ),
        ),
        _execution("openhcs_submit_compile", _completed_job("compile", "job-1")),
        _execution(
            "openhcs_submit_pipeline_execution",
            _completed_job("execute", "job-2"),
        ),
        _execution("openhcs_get_execution_status", _completed_job("execute", "job-2")),
    )
    recorder = McpAttemptRecorder(
        tmp_path / "evidence",
        _FakeMcpClient(executions),  # type: ignore[arg-type]
    )
    for execution in executions:
        recorder.execute(execution.argv)

    pipeline_path = tmp_path / "pipeline.py"
    pipeline_path.write_text(source)
    output_path = tmp_path / "case-1.npy"
    output_path.touch()
    record = recorder.finalize(
        AttemptObservation(
            attempt_id="attempt-1",
            task_id="human_eval_bia.expand_labels_without_overlap",
            phase=AttemptPhase.REVIEWED,
            pipeline_path=pipeline_path,
            output_paths=(output_path,),
            views=(),
            diagnostic_checks=frozenset({DiagnosticCheck.MISSED_SIGNAL}),
        )
    )

    observed = {artifact.requirement for artifact in record.dsl_evidence}
    assert observed == {
        DslRequirement.VARIABLE_COMPONENTS,
        DslRequirement.GROUP_BY,
        DslRequirement.SEQUENTIAL_FUNCTION_PATTERN,
        DslRequirement.ARTIFACT_MATERIALIZATION,
        DslRequirement.COMPILE_RUN_BOUNDARY,
        DslRequirement.SIGNATURE_DERIVED_EXPOSURE,
    }
    assert record.runtime is not None
    assert record.runtime.elapsed_seconds >= 0
    assert record.runtime.peak_rss_bytes > 0
    assert all(artifact.artifact_path.is_file() for artifact in record.dsl_evidence)


def test_failed_mcp_commands_do_not_create_semantic_evidence(tmp_path: Path):
    execution = _execution("openhcs_submit_compile", returncode=1)
    recorder = McpAttemptRecorder(
        tmp_path / "evidence",
        _FakeMcpClient((execution,)),  # type: ignore[arg-type]
    )
    recorder.execute(execution.argv)
    pipeline_path = tmp_path / "pipeline.py"
    pipeline_path.write_text(_pipeline_source())
    output_path = tmp_path / "case-1.npy"
    output_path.touch()
    record = recorder.finalize(
        AttemptObservation(
            attempt_id="attempt-1",
            task_id="human_eval_bia.expand_labels_without_overlap",
            phase=AttemptPhase.REVIEWED,
            pipeline_path=pipeline_path,
            output_paths=(output_path,),
            views=(),
            diagnostic_checks=frozenset(),
        )
    )
    assert record.dsl_evidence == ()


def test_structured_tool_failures_do_not_create_semantic_evidence(tmp_path: Path):
    execution = _failed_payload_execution("openhcs_submit_compile")
    recorder = McpAttemptRecorder(
        tmp_path / "evidence",
        _FakeMcpClient((execution,)),  # type: ignore[arg-type]
    )
    recorder.execute(execution.argv)
    pipeline_path = tmp_path / "pipeline.py"
    pipeline_path.write_text(_pipeline_source())
    output_path = tmp_path / "case-1.npy"
    output_path.touch()
    record = recorder.finalize(
        AttemptObservation(
            attempt_id="attempt-1",
            task_id="human_eval_bia.expand_labels_without_overlap",
            phase=AttemptPhase.REVIEWED,
            pipeline_path=pipeline_path,
            output_paths=(output_path,),
            views=(),
            diagnostic_checks=frozenset(),
        )
    )
    assert record.dsl_evidence == ()


def test_signature_projection_requires_the_same_function_identity(tmp_path: Path):
    source = _pipeline_source()
    entry = _function_entry()
    unrelated_ui_source = PipelineDocumentAuthority.render(
        PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(),
            pipeline_steps=[],
        )
    )
    executions = (
        _execution(
            "openhcs_register_custom_function",
            CustomFunctionRegistrationResult(
                schema_version="openhcs.agent.v1",
                registered_count=1,
                functions=(entry,),
            ),
        ),
        _execution(
            "openhcs_describe_function",
            FunctionDetail(
                schema_version="openhcs.agent.v1",
                entry=entry,
                parameters=(),
                doc=None,
            ),
        ),
        _execution("openhcs_add_function_step"),
        _execution("openhcs_validate_pipeline"),
        _execution(
            "openhcs_render_pipeline_source",
            RenderedSource(
                schema_version="openhcs.agent.v1",
                title="pipeline",
                source=source,
            ),
        ),
        _execution(
            "openhcs_ui_get_code_document",
            _ui_pipeline_document(unrelated_ui_source),
        ),
        _execution("openhcs_ui_apply_code_document"),
    )
    recorder = McpAttemptRecorder(tmp_path / "evidence", None)
    for execution in executions:
        recorder.preserve_execution(
            execution,
            elapsed_seconds=0.1,
            peak_rss_bytes=1024,
        )
    pipeline_path = tmp_path / "pipeline.py"
    pipeline_path.write_text(source)
    output_path = tmp_path / "case-1.npy"
    output_path.touch()
    record = recorder.finalize(
        AttemptObservation(
            attempt_id="attempt-1",
            task_id="human_eval_bia.expand_labels_without_overlap",
            phase=AttemptPhase.REVIEWED,
            pipeline_path=pipeline_path,
            output_paths=(output_path,),
            views=(),
            diagnostic_checks=frozenset(),
        )
    )
    observed = {artifact.requirement for artifact in record.dsl_evidence}
    assert DslRequirement.SIGNATURE_DERIVED_EXPOSURE not in observed
