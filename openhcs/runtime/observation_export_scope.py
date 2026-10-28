"""Runtime export choices shared by request declarations and execution."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta

if TYPE_CHECKING:
    from openhcs.core.compiled_execution import CompiledExecutionBundle


class ZMQRuntimeObservationExportScope(ABC, metaclass=AutoRegisterMeta):
    """Amount of runtime evidence requested from an ordinary execution.

    ``name`` is the scope's spelling on the wire and in agent requests.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    retains_runtime_values: ClassVar[bool]
    """Workers return their full runtime values for the export."""

    @classmethod
    def check_export_path(cls, export_path: object) -> None:
        """Reject a request that lacks the export path this scope needs."""

    @staticmethod
    def named(value: str) -> type[ZMQRuntimeObservationExportScope]:
        scope = ZMQRuntimeObservationExportScope.__registry__.get(value)
        if scope is None:
            raise ValueError(f"Unknown runtime observation export scope: {value!r}.")
        return scope

    @staticmethod
    @abstractmethod
    def export(
        *,
        execution_bundle: CompiledExecutionBundle,
        execution_results,
        output_roots,
        server_environment,
        execution_id: str,
    ):
        """Build this scope's runtime export from one finished execution."""


class ExportRuntimeValues(ZMQRuntimeObservationExportScope):
    """Export the full runtime values."""

    name = "values"
    retains_runtime_values = True

    @staticmethod
    def export(
        *, execution_bundle, execution_results, output_roots, server_environment, execution_id
    ):
        from openhcs.runtime.zmq_execution_observation import (
            ZMQRuntimeExecutionObservationExport,
        )

        return ZMQRuntimeExecutionObservationExport.from_execution(
            executed_contexts=execution_results.executed_contexts,
            execution_results=execution_results,
            runtime_observations=execution_results.runtime_observations,
            output_roots=output_roots,
            server_environment=server_environment,
            execution_id=execution_id,
        )


class ExportRuntimeOutcomes(ZMQRuntimeObservationExportScope):
    """Export per-axis outcomes and exports, without array values."""

    name = "outcomes"
    retains_runtime_values = False

    @classmethod
    def check_export_path(cls, export_path: object) -> None:
        if export_path is None:
            raise ValueError("Outcome observation requires an export path.")

    @staticmethod
    def export(
        *, execution_bundle, execution_results, output_roots, server_environment, execution_id
    ):
        from openhcs.core.runtime_exports import RuntimeExportObservation
        from openhcs.runtime.zmq_execution_observation import (
            ZMQRuntimeExecutionOutcomeExport,
        )

        return ZMQRuntimeExecutionOutcomeExport.from_execution(
            compiled_axis_ids=execution_bundle.runtime_contexts,
            execution_results=execution_results,
            output_roots=output_roots,
            server_environment=server_environment,
            execution_id=execution_id,
            exports=RuntimeExportObservation.from_runtime_observations(
                execution_results.runtime_observations
            ),
        )
