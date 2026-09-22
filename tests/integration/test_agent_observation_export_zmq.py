"""The agent's observation option uses ordinary pipeline execution end to end."""

from __future__ import annotations

import os
from pathlib import Path

from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.config_service import ConfigService
from openhcs.agent.services.execution_session_service import (
    ExecutionSessionService,
    PipelineSourceSessionRequest,
)
from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
)
from openhcs.runtime.zmq_execution_signature import ZMQExecutionIdentity


def test_headless_observation_export_uses_ordinary_execution(tmp_path: Path) -> None:
    plate = tmp_path / "plate"
    SyntheticMicroscopyGenerator(
        output_dir=str(plate),
        grid_size=(1, 1),
        tile_size=(32, 32),
        wavelengths=1,
        z_stack_levels=1,
        num_cells=2,
        wells=["A01"],
        format="ImageXpress",
        random_seed=7,
    ).generate_dataset()
    pipeline = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(),
        pipeline_steps=[
            FunctionStep(name="Blur", func=(gaussian_blur, {"sigma": 1.0}))
        ],
    )
    service = ExecutionSessionService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        ),
        pipeline_service=PipelineAuthoringService(),
        config_service=ConfigService(),
    )
    session = service.create_session_from_pipeline_source(
        PipelineSourceSessionRequest(
            identity=ZMQExecutionIdentity(plate_id=str(plate)),
            pipeline_source=PipelineDocumentAuthority.render(pipeline),
            global_config_id=None,
            connection=ExecutionConnectionSpec(
                port=18000 + os.getpid() % 20000,
                persistent=False,
            ),
        )
    )
    export_path = tmp_path / "runtime_observation.pkl"

    status = service.submit_execution(
        session.session_id,
        runtime_observation_export_path=str(export_path),
        wait=True,
        wait_timeout_ms=120_000,
    )

    assert status.status == "complete", status
    observation = ZMQRuntimeExecutionObservationExport.read(export_path)
    observation.require_valid_observation()
    assert observation.output_roots
