"""Drive one dataset through the headless session: add, initialize, compile, run.

Each stage invokes one session operation, then follows the session's events
(``openhcs_session_events`` blocks until something happens) and reads the
dataset row until the stage is over. Nothing here polls on a timer.
"""

from __future__ import annotations

import time
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import ClassVar

from python_introspect import JsonValue

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.session import DatasetListState, DatasetRowState
from openhcs.mcp.dev_client_core import (
    McpDevStdioSession,
    McpDevToolCall,
    McpDevToolResult,
    McpToolArguments,
    call_mcp_tool,
)

EVENT_WAIT_SECONDS = 5.0


class DatasetStage(ABC):
    """One step of the dataset workflow and when a dataset row has finished it."""

    capability: ClassVar[type]

    @classmethod
    @abstractmethod
    def finished(cls, row: DatasetRowState) -> bool: ...

    @classmethod
    @abstractmethod
    def succeeded(cls, row: DatasetRowState) -> bool: ...


class InitializeStage(DatasetStage):
    capability = agent_capabilities.initialize_datasets

    @classmethod
    def finished(cls, row: DatasetRowState) -> bool:
        return not row.init_pending and (
            row.initialized or row.orchestrator_state == "init_failed"
        )

    @classmethod
    def succeeded(cls, row: DatasetRowState) -> bool:
        return row.initialized


class CompileStage(DatasetStage):
    capability = agent_capabilities.compile_datasets

    @classmethod
    def finished(cls, row: DatasetRowState) -> bool:
        return not row.compile_pending and (
            row.compiled or row.orchestrator_state == "compile_failed"
        )

    @classmethod
    def succeeded(cls, row: DatasetRowState) -> bool:
        return row.compiled


class RunStage(DatasetStage):
    capability = agent_capabilities.run_datasets

    @classmethod
    def finished(cls, row: DatasetRowState) -> bool:
        return row.terminal_status is not None and not row.execution_active

    @classmethod
    def succeeded(cls, row: DatasetRowState) -> bool:
        return row.terminal_status == "complete"


@dataclass(slots=True)
class SessionJourney:
    """The calls of one journey, kept in order for rendering."""

    session: McpDevStdioSession
    timeout_seconds: float
    results: list[McpDevToolResult]

    async def call(self, capability, arguments: dict[str, JsonValue]) -> McpDevToolResult:
        result = await call_mcp_tool(
            self.session,
            McpDevToolCall(capability.name, McpToolArguments.from_payload(arguments)),
            self.timeout_seconds,
        )
        self.results.append(result)
        return result

    async def dataset_row(self, scope_id: str) -> DatasetRowState | None:
        result = await call_mcp_tool(
            self.session,
            McpDevToolCall(agent_capabilities.session_datasets.name, {}),
            self.timeout_seconds,
        )
        state = result.first_decoded_payload()
        if not isinstance(state, DatasetListState):
            return None
        return next((row for row in state.rows if row.scope_id == scope_id), None)

    async def wait_for(
        self,
        stage: type[DatasetStage],
        scope_id: str,
        *,
        after_sequence: int,
        timeout_seconds: float,
    ) -> DatasetRowState | None:
        """Follow session events until ``stage`` has finished for the dataset."""

        deadline = time.monotonic() + timeout_seconds
        sequence = after_sequence
        while True:
            row = await self.dataset_row(scope_id)
            if row is not None and stage.finished(row):
                return row
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return row
            events = await call_mcp_tool(
                self.session,
                McpDevToolCall(
                    agent_capabilities.session_events.name,
                    {
                        "after_sequence": sequence,
                        "timeout_seconds": min(EVENT_WAIT_SECONDS, remaining),
                    },
                ),
                self.timeout_seconds + EVENT_WAIT_SECONDS,
            )
            batch = events.first_decoded_payload()
            if batch is not None:
                sequence = batch.last_sequence

    async def run_source(
        self,
        *,
        root: str,
        pipeline_source: str,
        connection: ExecutionConnectionSpec,
        wait_for_run: bool,
        stage_timeout_seconds: float,
    ) -> None:
        """Add ``root``, give it ``pipeline_source``, initialize, compile and run it."""

        connected = await self.call(
            agent_capabilities.connect_server, connection.tool_arguments()
        )
        if _rejected(connected):
            return
        added = await self.call(agent_capabilities.add_datasets, {"roots": [root]})
        if _rejected(added):
            return
        (scope_id, *_rest) = added.first_decoded_payload().target_scope_ids
        piped = await self.call(
            agent_capabilities.set_dataset_pipeline,
            {"scope_id": scope_id, "pipeline_source": pipeline_source},
        )
        if _rejected(piped):
            return
        for stage in (InitializeStage, CompileStage, RunStage):
            started = await self.call(stage.capability, {"scope_ids": [scope_id]})
            if _rejected(started):
                return
            if stage is RunStage and not wait_for_run:
                return
            row = await self.wait_for(
                stage,
                scope_id,
                after_sequence=started.first_decoded_payload().event_sequence,
                timeout_seconds=stage_timeout_seconds,
            )
            if row is None or not stage.succeeded(row):
                break
        await self.call(agent_capabilities.session_datasets, {})


def _rejected(result: McpDevToolResult) -> bool:
    payload = result.first_decoded_payload()
    return payload is None or bool(payload.errors)
