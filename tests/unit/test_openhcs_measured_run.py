"""Measured runs wrap the ordinary pipeline submission, independent of CP."""

from __future__ import annotations

import hashlib
from pathlib import Path
from types import SimpleNamespace

import pytest

import benchmark.openhcs_measured_run as measured_run
from benchmark.contracts.measured_run_receipt import MeasuredPipelineRunReceipt
from benchmark.contracts.run_artifacts import MeasuredPipelineRunArtifact
from benchmark.contracts.tool_adapter import ToolExecutionError
from benchmark.timing import BenchmarkPhase, PhaseTimingTrace
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.orchestrator.execution_result import ExecutionResult
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.runtime.zmq_application import OPENHCS_ENDPOINT_APPLICATION
from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission
from openhcs.runtime.zmq_execution_observation import ZMQRuntimeExecutionOutcomeExport
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
    ZMQRuntimeObservationExportScope,
)


@pytest.mark.parametrize("valid_observation", (True, False))
def test_measured_run_validates_an_ordinary_pipeline_document(
    monkeypatch, tmp_path: Path, valid_observation: bool
) -> None:
    observation_path = tmp_path / "observation.pkl"
    document = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(), pipeline_steps=[]
    )
    submission = OpenHCSExecutionSubmission(
        plate_id=tmp_path,
        pipeline_document=document,
        global_config=GlobalPipelineConfig(),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(runtime_observation_export_path=observation_path)
    )
    clients = []

    class FakeClient:
        def __init__(self, *, port, persistent, progress_callback):
            assert port is None
            assert persistent is False
            self.connected_endpoint = SimpleNamespace(
                application=OPENHCS_ENDPOINT_APPLICATION,
                process_identity=None,
                log_file_path=None,
                port=5555,
            )
            self.disconnect_count = 0
            clients.append(self)

        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc, traceback):
            self.disconnect()
            return None

        def disconnect(self):
            self.disconnect_count += 1

        def submit_compile(self, submitted):
            assert submitted.pipeline_document is submission.pipeline_document
            return {"status": "accepted", "execution_id": "compile-1"}

        def submit_pipeline(self, submitted):
            assert submitted.pipeline_document is submission.pipeline_document
            assert submitted.compile_artifact_id == "compile-1"
            assert (
                ZMQAuxiliaryExecutionParams.from_transport(
                    submitted.config_params
                ).runtime_observation_export_path
                == observation_path
            )
            return {"status": "accepted", "execution_id": "execute-1"}

        def wait_for_completion(self, execution_id):
            if execution_id == "execute-1":
                observation_path.touch()
            return {
                "status": "complete",
                "execution_id": execution_id,
                "results": {"output_plate_root": str(tmp_path)},
            }

        def poll_status(self, execution_id):
            return {
                "status": "ok",
                "execution": {
                    "execution_id": execution_id,
                    "plate_id": str(tmp_path),
                    "client_address": None,
                    "status": "complete",
                    "start_time": 10.0,
                    "end_time": 12.0,
                },
            }

    monkeypatch.setattr(measured_run, "ZMQExecutionClient", FakeClient)

    def validate_observation():
        if not valid_observation:
            raise RuntimeError("compiled expectation failed")
        return SimpleNamespace(records_by_axis={})

    monkeypatch.setattr(
        measured_run,
        "ZMQRuntimeExecutionObservationExport",
        SimpleNamespace(
            read=lambda path: SimpleNamespace(
                output_roots=(tmp_path,),
                axis_count=1,
                execution_id="execute-1",
                server_environment=None,
                require_valid_observation=validate_observation,
            )
        ),
    )
    timing = PhaseTimingTrace(run_id="ordinary", pipeline_name="empty", tool="OpenHCS")

    if not valid_observation:
        with pytest.raises(ToolExecutionError, match="compiled expectation failed"):
            measured_run.execute_measured_openhcs_pipeline(
                submission=submission,
                phase_timing=timing,
                timing_observer=measured_run._ZMQProgressTimingObserver(),
            )
        assert clients[0].disconnect_count == 1
        assert not (tmp_path / measured_run.ZMQ_RESULTS_SUMMARY_FILENAME).exists()
        assert not MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path).exists()
        return

    result, source = measured_run.execute_measured_openhcs_pipeline(
        submission=submission,
        phase_timing=timing,
        timing_observer=measured_run._ZMQProgressTimingObserver(),
    )

    assert result.execution_id == "execute-1"
    assert clients[0].disconnect_count == 1
    assert result.output_roots == (tmp_path,)
    assert result.observation.records_by_axis == {}
    assert source == submission.pipeline_code()
    retained = MeasuredPipelineRunReceipt.read(
        MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path)
    )
    assert retained == result.receipt
    assert retained.compile_artifact_id == "compile-1"
    assert (
        retained.pipeline_source_sha256
        == hashlib.sha256(source.encode("utf-8")).hexdigest()
    )
    assert (
        MeasuredPipelineRunArtifact.PIPELINE_SOURCE.path_in(tmp_path).read_text(
            encoding="utf-8"
        )
        == source
    )
    assert (
        retained.global_config_source_sha256
        == hashlib.sha256(
            MeasuredPipelineRunArtifact.GLOBAL_CONFIG_SOURCE.path_in(
                tmp_path
            ).read_bytes()
        ).hexdigest()
    )
    assert [record.phase for record in timing.records] == [
        BenchmarkPhase.SUBMIT_OPENHCS,
        BenchmarkPhase.WAIT_OPENHCS,
        BenchmarkPhase.SUBMIT_OPENHCS,
        BenchmarkPhase.WAIT_OPENHCS,
        BenchmarkPhase.SERVER_COMPILATION_JOB,
        BenchmarkPhase.SERVER_PIPELINE_JOB,
        BenchmarkPhase.EXECUTE_OPENHCS,
        BenchmarkPhase.VALIDATE_RUNTIME,
    ]


def test_shared_evidence_writer_never_overwrites_existing_artifact(
    monkeypatch, tmp_path: Path
) -> None:
    observation_path = tmp_path / "observation.pkl"
    observation_path.touch()
    existing_source = MeasuredPipelineRunArtifact.PIPELINE_SOURCE.path_in(tmp_path)
    existing_source.write_text("keep this evidence", encoding="utf-8")
    submission = OpenHCSExecutionSubmission(
        plate_id=tmp_path,
        pipeline_document=PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(), pipeline_steps=[]
        ),
        global_config=GlobalPipelineConfig(),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(runtime_observation_export_path=observation_path)
    )
    monkeypatch.setattr(
        measured_run,
        "ZMQRuntimeExecutionObservationExport",
        SimpleNamespace(
            read=lambda path: SimpleNamespace(
                output_roots=(tmp_path,),
                execution_id="execution-1",
                require_valid_observation=lambda: SimpleNamespace(records_by_axis={}),
            )
        ),
    )
    endpoint = measured_run.measured_endpoint_provenance(
        SimpleNamespace(
            application=OPENHCS_ENDPOINT_APPLICATION,
            process_identity=None,
            log_file_path=None,
            port=5555,
        )
    )

    with pytest.raises(FileExistsError, match="Measured run evidence already exists"):
        measured_run.retain_measured_openhcs_completion(
            submission=submission,
            execution_id="execution-1",
            results_summary={},
            endpoint_provenance=endpoint,
            phase_timing=PhaseTimingTrace(
                run_id="ordinary", pipeline_name="empty", tool="OpenHCS"
            ),
            compile_artifact_id=None,
        )

    assert existing_source.read_text(encoding="utf-8") == "keep this evidence"
    assert not MeasuredPipelineRunArtifact.RESULTS_SUMMARY.path_in(tmp_path).exists()
    assert not MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path).exists()


def test_outcome_only_run_uses_the_shared_receipt_finalizer(tmp_path: Path) -> None:
    observation_path = tmp_path / "outcomes.pkl.gz"
    ZMQRuntimeExecutionOutcomeExport.from_execution(
        execution_results={"A01": ExecutionResult.success("A01")},
        output_roots=(tmp_path / "output",),
        execution_id="execution-1",
    ).write(observation_path)
    submission = OpenHCSExecutionSubmission(
        plate_id=tmp_path,
        pipeline_document=PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(), pipeline_steps=[]
        ),
        global_config=GlobalPipelineConfig(materialize_runtime_artifacts=False),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=observation_path,
            runtime_observation_export_scope=ZMQRuntimeObservationExportScope.OUTCOMES,
        )
    )
    endpoint = measured_run.measured_endpoint_provenance(
        SimpleNamespace(
            application=OPENHCS_ENDPOINT_APPLICATION,
            process_identity=None,
            log_file_path=None,
            port=5555,
        )
    )

    with pytest.raises(ToolExecutionError, match="execution identity does not match"):
        measured_run.retain_measured_openhcs_completion(
            submission=submission,
            execution_id="stale-job",
            results_summary={"well_count": 1},
            endpoint_provenance=endpoint,
            phase_timing=PhaseTimingTrace(
                run_id="outcome-run", pipeline_name="empty", tool="OpenHCS"
            ),
            compile_artifact_id="compile-1",
        )
    assert not MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path).exists()

    with pytest.raises(ToolExecutionError, match="Expected 2 execution axes"):
        measured_run.retain_measured_openhcs_completion(
            submission=submission,
            execution_id="execution-1",
            results_summary={"well_count": 1},
            endpoint_provenance=endpoint,
            phase_timing=PhaseTimingTrace(
                run_id="outcome-run", pipeline_name="empty", tool="OpenHCS"
            ),
            compile_artifact_id="compile-1",
            expected_axis_count=2,
        )
    assert not MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path).exists()

    completion = measured_run.retain_measured_openhcs_completion(
        submission=submission,
        execution_id="execution-1",
        results_summary={"well_count": 1},
        endpoint_provenance=endpoint,
        phase_timing=PhaseTimingTrace(
            run_id="outcome-run", pipeline_name="empty", tool="OpenHCS"
        ),
        compile_artifact_id="compile-1",
        expected_axis_count=1,
    )

    assert completion.observation is None
    assert completion.axis_count == 1
    assert completion.receipt.expected_axis_count == 1
    assert completion.receipt.observed_axis_count == 1
    assert (
        completion.receipt.observation_export_scope
        is ZMQRuntimeObservationExportScope.OUTCOMES
    )
    assert (
        MeasuredPipelineRunReceipt.read(
            MeasuredPipelineRunArtifact.RECEIPT.path_in(tmp_path)
        )
        == completion.receipt
    )


def test_measured_run_refuses_to_reuse_an_unowned_server(
    monkeypatch, tmp_path: Path
) -> None:
    class AttachedClient:
        def __init__(self, **_kwargs):
            self.connected_endpoint = SimpleNamespace(
                application=OPENHCS_ENDPOINT_APPLICATION,
                process_identity=None,
                log_file_path=None,
                port=5555,
            )

        def __enter__(self):
            return self

        def __exit__(self, *_args):
            return None

        def owned_server_process_is_alive(self):
            return None

    monkeypatch.setattr(measured_run, "ZMQExecutionClient", AttachedClient)
    submission = OpenHCSExecutionSubmission(
        plate_id=tmp_path,
        pipeline_document=PipelineDocumentAuthority.from_values(
            pipeline_config=PipelineConfig(), pipeline_steps=[]
        ),
        global_config=GlobalPipelineConfig(),
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=tmp_path / "observation.pkl.gz"
        )
    )

    with pytest.raises(ToolExecutionError, match="client-owned execution server"):
        measured_run.execute_measured_openhcs_pipeline(
            submission=submission,
            phase_timing=PhaseTimingTrace(
                run_id="unowned", pipeline_name="empty", tool="OpenHCS"
            ),
            timing_observer=measured_run._ZMQProgressTimingObserver(),
            require_owned_server=True,
        )
