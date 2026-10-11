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
    dataset_root: str


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
            dataset_root=self.prepared_dataset_root(storage_registry),
        )

    def prepared_dataset_root(self, storage_registry) -> str:
        from openhcs.core.dataset_sources.dataset_roots import DatasetRootRule

        dataset_root = str(
            self.subject_id
            if self.execution_subject_id is None
            else self.execution_subject_id
        )
        return DatasetRootRule.for_dataset(dataset_root).prepare_storage(
            dataset_root, storage_registry
        )
