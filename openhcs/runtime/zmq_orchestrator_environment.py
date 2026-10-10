"""Environment preparation for ZMQ orchestrator execution."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from openhcs.runtime.zmq_execution_signature import ZMQExecutionIdentity

if TYPE_CHECKING:
    from openhcs.core.debug import DebugExecutionConfig, DebugExecutionPolicy


@dataclass(frozen=True, slots=True)
class ZMQOrchestratorEnvironment:
    """Prepared execution environment for one ZMQ orchestrator run."""

    debug_execution_policy: DebugExecutionPolicy
    debug_execution_config: DebugExecutionConfig | None
    plate_path_str: str


@dataclass(frozen=True, slots=True, kw_only=True)
class ZMQOrchestratorEnvironmentRequest(ZMQExecutionIdentity):
    """Inputs needed to prepare the worker execution environment."""

    execution_id: str
    debug_execution_config: DebugExecutionConfig | None

    def prepare(self) -> ZMQOrchestratorEnvironment:
        from polystore.base import reset_memory_backend, storage_registry

        from openhcs.core.debug import DebugExecutionPolicy

        reset_memory_backend()

        debug_execution_policy = DebugExecutionPolicy.from_config(
            self.debug_execution_config
        )

        return ZMQOrchestratorEnvironment(
            debug_execution_policy=debug_execution_policy,
            debug_execution_config=self.debug_execution_config,
            plate_path_str=self.prepared_plate_path(storage_registry),
        )

    def prepared_plate_path(self, storage_registry) -> str:
        from openhcs.core.dataset_sources.dataset_roots import DatasetRootRule

        plate_path_str = str(
            self.plate_id if self.execution_plate_id is None else self.execution_plate_id
        )
        return DatasetRootRule.for_dataset(plate_path_str).prepare_storage(
            plate_path_str, storage_registry
        )
