"""Debug executions: compile reuse, submission, worker commands and export."""

from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import TYPE_CHECKING

from python_introspect import project_dataclass

from openhcs.authoring.session.compilation import DatasetPipelineRequest, run_blocking
from openhcs.authoring.session.events import StatusReported
from openhcs.core.debug import (
    DebugArtifactExportResponse,
    DebugArtifactRef,
    DebugCommandType,
    DebugExecutionConfig,
    DebugPausedWorkerStatus,
    DebugReplayMode,
)
from openhcs.runtime.zmq_execution_client import ZMQExecutionRequestBuilder
from openhcs.core.debug import WarmArtifactReplay

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session

logger = logging.getLogger(__name__)


@dataclass(frozen=True, kw_only=True)
class DebugRunRequest:
    """Debug execution identity threaded through compile and run submission."""

    debug_session_id: str
    snapshot_store_ref: str
    snapshot_store_backend: str | None
    command_type: type[DebugCommandType]
    pause_step_indices: tuple[int, ...]
    selected_source_group: str | None
    replay_mode: type[DebugReplayMode] = WarmArtifactReplay
    start_step_index: int = 0
    start_after_invocation_key: str | None = None

    @property
    def execution_config(self) -> DebugExecutionConfig:
        return project_dataclass(DebugExecutionConfig, self)

    @property
    def compile_config_params(self) -> dict:
        return self.execution_config.compile_cache_config_params()


class DebugRuns:
    """Owns debug compile reuse, debug submission, worker controls and export."""

    def __init__(self, session: "Session") -> None:
        self._session = session
        self._compile_artifacts: dict[str, str] = {}

    async def compile_artifact_id(
        self,
        request: DatasetPipelineRequest,
        debug_request: DebugRunRequest,
    ) -> str:
        debug_compile_request = request.with_config_params(
            debug_request.compile_config_params
        )
        signature = ZMQExecutionRequestBuilder.from_task(
            debug_compile_request.submission()
        ).request_payload.debug_replay_signature
        retains = debug_request.replay_mode.retains_compile_artifact
        if retains and signature in self._compile_artifacts:
            artifact_id = self._compile_artifacts[signature]
            logger.info(
                "Reusing debug compile artifact: dataset=%s artifact_id=%s",
                request.scope_id,
                artifact_id,
            )
            return artifact_id
        artifacts = await self._session.compile_batch.compile_before_execution(
            [request],
            {request.scope_id: debug_request.compile_config_params},
        )
        artifact_id = artifacts[request.scope_id]
        if retains:
            self._compile_artifacts[signature] = artifact_id
        return artifact_id

    async def submit(
        self,
        request: DatasetPipelineRequest,
        *,
        compile_artifact_id: str,
        debug_request: DebugRunRequest,
    ) -> None:
        await self._session.submission.submit_debug(
            request,
            compile_artifact_id=compile_artifact_id,
            debug_config=debug_request.execution_config,
        )

    async def send_worker_command(
        self,
        *,
        debug_session_id: str,
        command_type: type[DebugCommandType],
    ) -> DebugPausedWorkerStatus:
        client = self._session.client.require_client()
        status = await run_blocking(
            lambda: client.send_debug_worker_command(
                debug_session_id=debug_session_id,
                command_type=command_type,
            ).worker
        )
        self._session.publish(
            StatusReported(
                f"Debug worker {status.state.name} for session {debug_session_id[:8]}"
            )
        )
        return status

    async def inspect_runtime(self, *, debug_session_id: str):
        client = self._session.client.require_client()
        view_model = await run_blocking(
            lambda: client.get_debug_runtime_inspection(
                debug_session_id=debug_session_id,
            )
        )
        self._session.publish(
            StatusReported(f"Loaded runtime inspection for session {debug_session_id[:8]}")
        )
        return view_model

    async def export_artifact(
        self,
        *,
        debug_session_id: str,
        artifact_ref: DebugArtifactRef,
        export_root: str,
        snapshot_store_ref: str | None,
        snapshot_store_backend: str | None,
    ) -> DebugArtifactExportResponse:
        client = self._session.client.require_client()
        response = await run_blocking(
            lambda: client.export_debug_artifact(
                debug_session_id=debug_session_id,
                artifact_ref=artifact_ref,
                export_root=export_root,
                snapshot_store_ref=snapshot_store_ref,
                snapshot_store_backend=snapshot_store_backend,
            )
        )
        self._session.publish(
            StatusReported(f"Exported debug artifact to {response.exported_ref}")
        )
        return response
