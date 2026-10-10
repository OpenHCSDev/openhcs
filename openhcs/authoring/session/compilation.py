"""Compile requests for one dataset and their submission to the execution server."""

from __future__ import annotations

import asyncio
import hashlib
import logging
from collections.abc import Callable
from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, TypeVar

from zmqruntime.execution import ExecutionSubmissionResponse, ExecutionWaitResult

from openhcs.core.artifact_inspection import CompiledArtifactInspection
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.dataset_sources.dataset_scopes import DatasetScope
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission
from openhcs.runtime.zmq_execution_signature import (
    TransportValue,
    ZMQAuxiliaryExecutionParams,
)

if TYPE_CHECKING:
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

logger = logging.getLogger(__name__)
T = TypeVar("T")


async def run_blocking(function: Callable[[], T]) -> T:
    """Run blocking transport work off the running event loop."""

    return await asyncio.get_running_loop().run_in_executor(None, function)


def pipeline_fingerprint(steps: list) -> str:
    source = FunctionStepTransportAuthority.source_from_pipeline(
        FunctionStepTransportAuthority.normalize_pipeline(steps)
    )
    return hashlib.sha256(source.encode("utf-8")).hexdigest()[:12]


@dataclass(frozen=True)
class DatasetPipelineRequest:
    """One dataset's pipeline, configs and execution paths, ready to submit."""

    scope: DatasetScope
    name: str
    execution_root: str
    pipeline_path: str | None
    steps: list
    pipeline_config: PipelineConfig
    global_config: GlobalPipelineConfig
    config_params: dict[str, TransportValue] | None = None

    @property
    def scope_id(self) -> str:
        return self.scope.scope_id

    def with_config_params(
        self,
        config_params: dict[str, TransportValue] | None,
    ) -> "DatasetPipelineRequest":
        return replace(self, config_params=config_params)

    def submission(
        self,
        *,
        compile_artifact_id: str | None = None,
        auxiliary_params: ZMQAuxiliaryExecutionParams | None = None,
    ) -> OpenHCSExecutionSubmission:
        submission = OpenHCSExecutionSubmission(
            plate_id=self.scope_id,
            execution_plate_id=self.execution_root,
            selected_pipeline_path=self.pipeline_path,
            pipeline_document=PipelineDocumentCodec.from_values(
                pipeline_config=self.pipeline_config,
                pipeline_steps=FunctionStepTransportAuthority.normalize_pipeline(
                    self.steps
                ),
            ),
            global_config=self.global_config,
            compile_artifact_id=compile_artifact_id,
            config_params=self.config_params,
        )
        if auxiliary_params is None:
            return submission
        return submission.with_auxiliary_params(auxiliary_params)


@dataclass(frozen=True, slots=True)
class CompiledDataset:
    """What one successful compilation leaves on the session."""

    compile_artifact_id: str
    steps: tuple
    inspection: CompiledArtifactInspection

    def __post_init__(self) -> None:
        if self.compile_artifact_id != self.inspection.compile_artifact_id:
            raise ValueError(
                "CompiledDataset compile artifact identity does not match its "
                "inspection."
            )


async def submit_compile(
    client: "ZMQExecutionClient",
    request: DatasetPipelineRequest,
) -> str:
    """Submit one compile job; return its execution id."""

    def submit() -> dict:
        logger.info(
            "Submit compile: dataset=%s execution_root=%s steps=%d fingerprint=%s",
            request.scope_id,
            request.execution_root,
            len(request.steps),
            pipeline_fingerprint(request.steps),
        )
        return client.submit_compile(request.submission())

    response = ExecutionSubmissionResponse.from_wire(await run_blocking(submit))
    if not response.accepted:
        raise RuntimeError(
            f"Compile submission failed for {request.scope_id}: "
            f"{response.require_failure_text('Compile submission')}"
        )
    return response.require_execution_id("Compile submission")


async def wait_for_compile(
    client: "ZMQExecutionClient",
    *,
    execution_id: str,
    scope_id: str,
) -> CompiledArtifactInspection:
    """Wait for one compile job and fetch the compiler's artifact inspection."""

    wait_result = ExecutionWaitResult.from_wire(
        await run_blocking(lambda: client.wait_for_completion(execution_id))
    )
    wait_result.require_complete(f"Compilation failed for {scope_id}")
    return await run_blocking(
        lambda: client.get_compiled_artifact_inspection(execution_id)
    )
