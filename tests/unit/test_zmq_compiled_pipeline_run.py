"""Ordinary compile-then-execute lifecycle used by measured runs."""

from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path

import pytest

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.debug import DebugExecutionConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQPipelineRunPhase,
    run_compiled_pipeline,
)
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams


class FakeExecutionClient:
    def __init__(self, *, compile_status="complete", execute_status="complete"):
        self.compile_status = compile_status
        self.execute_status = execute_status
        self.events = []
        self.compile_submission = None
        self.execution_submission = None

    def submit_compile(self, submission):
        self.events.append("submit_compile")
        self.compile_submission = submission
        return {"status": "accepted", "execution_id": "compile-1"}

    def submit_pipeline(self, submission):
        self.events.append("submit_execution")
        self.execution_submission = submission
        return {"status": "accepted", "execution_id": "execute-1"}

    def wait_for_completion(self, execution_id):
        self.events.append(f"wait:{execution_id}")
        return {
            "status": (
                self.compile_status
                if execution_id == "compile-1"
                else self.execute_status
            ),
            "execution_id": execution_id,
        }


class RejectingCompileClient(FakeExecutionClient):
    def submit_compile(self, submission):
        self.events.append("submit_compile")
        return {"status": "error", "error": "compile rejected"}


def _submission():
    return OpenHCSExecutionSubmission(
        plate_id="/tmp/plate",
        pipeline_document=PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(), pipeline_steps=[]
        ),
        global_config=GlobalPipelineConfig(),
    )


def test_compiled_pipeline_run_uses_one_document_and_source_owned_phases():
    client = FakeExecutionClient()
    submission = _submission()
    observed_phases = []

    @contextmanager
    def observe(phase):
        observed_phases.append(("start", phase))
        try:
            yield
        finally:
            observed_phases.append(("end", phase))

    result = run_compiled_pipeline(client, submission, phase_context=observe)

    assert result.compile_artifact_id == "compile-1"
    assert result.execution_id == "execute-1"
    assert result.completion_response["status"] == "complete"
    assert result.completion_observed_at > 0
    assert client.events == [
        "submit_compile",
        "wait:compile-1",
        "submit_execution",
        "wait:execute-1",
    ]
    assert client.execution_submission.pipeline_document is submission.pipeline_document
    assert client.execution_submission.compile_artifact_id == "compile-1"
    assert observed_phases == [
        (event, phase) for phase in ZMQPipelineRunPhase for event in ("start", "end")
    ]


def test_auxiliary_observation_request_is_shared_by_client_and_server():
    path = Path("/tmp/observation.pkl")
    submission = _submission().with_config_params({"unrelated": "kept"})

    observed = submission.with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(runtime_observation_export_path=path)
    )
    compiled = observed.compile_request()
    execution = compiled.with_compile_artifact_id("compiled-1")

    assert submission.config_params == {"unrelated": "kept"}
    assert execution.pipeline_document is submission.pipeline_document
    assert execution.config_params == {
        "unrelated": "kept",
        "runtime_observation_export_path": str(path),
    }
    assert (
        ZMQAuxiliaryExecutionParams.from_transport(
            execution.config_params
        ).runtime_observation_export_path
        == path
    )


def test_auxiliary_options_round_trip_through_one_transport_declaration():
    options = ZMQAuxiliaryExecutionParams(
        axis_filter=("A01", "B02"),
        debug_execution_config=DebugExecutionConfig(debug_session_id="debug-1"),
        runtime_observation_export_path=Path("/tmp/observed.pkl"),
    )

    assert ZMQAuxiliaryExecutionParams.from_transport(options.to_transport()) == options


def test_compiled_pipeline_run_stops_before_execution_when_compile_fails():
    client = FakeExecutionClient(compile_status="failed")

    with pytest.raises(RuntimeError, match="compilation failed"):
        run_compiled_pipeline(client, _submission())

    assert client.events == ["submit_compile", "wait:compile-1"]
    assert client.execution_submission is None


def test_compiled_pipeline_run_stops_when_compile_submission_is_rejected():
    client = RejectingCompileClient()

    with pytest.raises(RuntimeError, match="compile rejected"):
        run_compiled_pipeline(client, _submission())

    assert client.events == ["submit_compile"]


def test_compiled_pipeline_run_does_not_report_failed_execution_as_complete():
    client = FakeExecutionClient(execute_status="failed")

    with pytest.raises(RuntimeError, match="execution failed"):
        run_compiled_pipeline(client, _submission())

    assert client.events[-1] == "wait:execute-1"
