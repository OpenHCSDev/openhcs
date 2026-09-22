"""Measured runs wrap the ordinary pipeline submission, independent of CP."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest
from zmqruntime import EndpointApplication, EndpointApplicationCompatibility

import benchmark.openhcs_measured_run as measured_run
from benchmark.contracts.tool_adapter import ToolExecutionError
from benchmark.timing import BenchmarkPhase, PhaseTimingTrace
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams


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
                application=EndpointApplication("openhcs", "test"),
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

        def endpoint_compatibility(self):
            application = self.connected_endpoint.application
            return EndpointApplicationCompatibility(
                expected=application, observed=application
            )

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
    assert [record.phase for record in timing.records] == [
        BenchmarkPhase.SUBMIT_OPENHCS,
        BenchmarkPhase.WAIT_OPENHCS,
        BenchmarkPhase.SUBMIT_OPENHCS,
        BenchmarkPhase.WAIT_OPENHCS,
        BenchmarkPhase.EXECUTE_OPENHCS,
        BenchmarkPhase.VALIDATE_RUNTIME,
    ]
