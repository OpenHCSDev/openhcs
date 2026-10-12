"""Typed request signatures for ZMQ execution and debug replay."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING, Any, ClassVar

from metaclass_registry import AutoRegisterMeta

from zmqruntime.messages import ExecuteRequest, MessageFields

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.orchestrator.execution_result import RuntimeObservationMode
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
    ZMQRuntimeExecutionOutcomeExport,
)

if TYPE_CHECKING:
    from openhcs.core.compiled_execution import CompiledExecutionBundle
    from openhcs.core.debug import DebugExecutionConfig

TransportValue = (
    str
    | int
    | float
    | bool
    | None
    | Mapping[str, "TransportValue"]
    | tuple["TransportValue", ...]
)
TransportRequestItems = tuple[tuple[str, TransportValue], ...]


class ZMQAuxiliaryParamField(Enum):
    """Transport keys consumed as typed auxiliary execution inputs."""

    PARTITION_VALUES = "partition_values"
    RUNTIME_OBSERVATION_EXPORT_PATH = "runtime_observation_export_path"
    RUNTIME_OBSERVATION_EXPORT_SCOPE = "runtime_observation_export_scope"
    PREPARE_WORKERS_ONLY = "prepare_workers_only"


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


@dataclass(frozen=True, slots=True)
class ZMQAuxiliaryExecutionParams:
    """Auxiliary execution options shared by the ordinary client and server."""

    partition_values: tuple[str, ...] | None = None
    debug_execution_config: DebugExecutionConfig | None = None
    runtime_observation_export_path: Path | None = None
    runtime_observation_export_scope: type[ZMQRuntimeObservationExportScope] = (
        ExportRuntimeValues
    )
    # "Prepare this pipeline": load what the compiled pipeline selects into the
    # workers that will run it, and execute nothing.
    prepare_workers_only: bool = False

    def __post_init__(self) -> None:
        self.runtime_observation_export_scope.check_export_path(
            self.runtime_observation_export_path
        )

    def runtime_observation_mode_for(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> type[RuntimeObservationMode]:
        """Resolve retention from compiled needs plus an explicit export request."""

        return RuntimeObservationMode.for_compiled_bundle(
            execution_bundle
        ).including_parent_requirement(
            self.runtime_observation_export_path is not None
            and self.runtime_observation_export_scope.retains_runtime_values
        )

    def to_transport(self) -> dict[str, Any]:
        """Project explicitly requested options into zmqruntime config_params."""

        params: dict[str, Any] = {}
        if self.partition_values is not None:
            params[ZMQAuxiliaryParamField.PARTITION_VALUES.value] = list(self.partition_values)
        if self.debug_execution_config is not None:
            params.update(self.debug_execution_config.to_config_params())
        if self.runtime_observation_export_path is not None:
            params.update(self.runtime_observation_items())
        if self.prepare_workers_only:
            params[ZMQAuxiliaryParamField.PREPARE_WORKERS_ONLY.value] = True
        return params

    def runtime_observation_items(self) -> TransportRequestItems:
        """Project the complete observation-only field family, including defaults."""

        return (
            (
                ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value,
                (
                    None
                    if self.runtime_observation_export_path is None
                    else str(self.runtime_observation_export_path)
                ),
            ),
            (
                ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_SCOPE.value,
                self.runtime_observation_export_scope.name,
            ),
        )

    @classmethod
    def compilation_config_params(
        cls, config_params: Mapping[str, Any] | None
    ) -> dict[str, Any] | None:
        """Exclude only fields owned by the runtime observation projection."""

        auxiliary = cls.from_transport(config_params)
        if config_params is None:
            return None
        not_compiled = {
            *dict(auxiliary.runtime_observation_items()),
            ZMQAuxiliaryParamField.PREPARE_WORKERS_ONLY.value,
        }
        return {
            key: value
            for key, value in config_params.items()
            if key not in not_compiled
        } or None

    @classmethod
    def from_transport(
        cls,
        config_params: Mapping[str, Any] | None,
    ) -> ZMQAuxiliaryExecutionParams:
        if not config_params:
            return cls()
        return cls(
            partition_values=cls._partition_values_from_transport(
                config_params.get(ZMQAuxiliaryParamField.PARTITION_VALUES.value)
            ),
            debug_execution_config=cls._debug_config_from_transport(config_params),
            runtime_observation_export_path=cls._path_from_transport(
                config_params.get(
                    ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value
                )
            ),
            runtime_observation_export_scope=cls._scope_from_transport(
                config_params.get(
                    ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_SCOPE.value
                )
            ),
            prepare_workers_only=config_params.get(
                ZMQAuxiliaryParamField.PREPARE_WORKERS_ONLY.value
            )
            is True,
        )

    @staticmethod
    def _scope_from_transport(
        value: str | None,
    ) -> type[ZMQRuntimeObservationExportScope]:
        if value is None:
            return ExportRuntimeValues
        return ZMQRuntimeObservationExportScope.named(value)

    @staticmethod
    def _partition_values_from_transport(
        partition_values: list[str] | tuple[str, ...] | str | int | None,
    ) -> tuple[str, ...] | None:
        if partition_values is None:
            return None
        if isinstance(partition_values, list):
            return tuple(str(axis_id) for axis_id in partition_values)
        if isinstance(partition_values, tuple):
            return tuple(str(axis_id) for axis_id in partition_values)
        raise TypeError(
            "ZMQ config_params partition_values must be a concrete axis-id sequence, "
            f"got {type(partition_values).__name__}."
        )

    @staticmethod
    def _debug_config_from_transport(
        config_params: Mapping[str, Any],
    ) -> DebugExecutionConfig | None:
        from openhcs.core.debug import DebugExecutionConfig

        payload = config_params.get(DebugExecutionConfig.CONFIG_PARAMS_KEY)
        if payload is None:
            return None
        return DebugExecutionConfig.from_payload(payload)

    @staticmethod
    def _path_from_transport(value: str | Path | None) -> Path | None:
        if value is None:
            return None
        if isinstance(value, Path):
            return value
        if isinstance(value, str):
            return Path(value)
        raise TypeError(
            "ZMQ config_params runtime observation export path must be a path "
            f"string, got {type(value).__name__}."
        )


@dataclass(frozen=True, slots=True)
class OpenHCSExecutionConfigBundle:
    """Global execution context plus the config projected from a pipeline document."""

    global_pipeline: GlobalPipelineConfig
    pipeline: PipelineConfig


@dataclass(frozen=True, slots=True)
class ZMQExecutionIdentity:
    """Subject and source-selection identity shared by client and server."""

    subject_id: str
    execution_subject_id: str | None = None
    selected_pipeline_path: str | None = None

    def signature_items(self) -> TransportRequestItems:
        return (
            (MessageFields.SUBJECT_ID, self.subject_id),
            (MessageFields.EXECUTION_SUBJECT_ID, self.execution_subject_id),
            (MessageFields.SELECTED_PIPELINE_PATH, self.selected_pipeline_path),
        )


@dataclass(frozen=True, slots=True)
class ZMQExecutionCompileControl:
    """Compile-mode controls shared by client and server requests."""

    compile_artifact_id: str | None = None
    compile_only: bool = False

    @classmethod
    def from_execute_request(
        cls,
        request: ExecuteRequest,
    ) -> "ZMQExecutionCompileControl":
        return cls(
            compile_artifact_id=request.compile_artifact_id,
            compile_only=request.compile_only,
        )

    def as_compile_request(self) -> "ZMQExecutionCompileControl":
        return ZMQExecutionCompileControl(
            compile_artifact_id=self.compile_artifact_id,
            compile_only=True,
        )

    def as_execution_request(
        self, compile_artifact_id: str
    ) -> "ZMQExecutionCompileControl":
        if not compile_artifact_id:
            raise ValueError("compile_artifact_id cannot be empty")
        return ZMQExecutionCompileControl(compile_artifact_id=compile_artifact_id)

    def validate(self) -> None:
        if self.compile_only and self.compile_artifact_id:
            raise ValueError("compile_only and compile_artifact_id cannot both be set")


@dataclass(frozen=True, slots=True)
class ZMQExecutionConfigTransport:
    """Global-config source plus auxiliary transport params for request signatures."""

    config_params: dict | None = None
    config_code: str | None = None

    @classmethod
    def from_execute_request(
        cls,
        request: ExecuteRequest,
    ) -> "ZMQExecutionConfigTransport":
        return cls(
            config_params=request.config_params,
            config_code=request.config_code,
        )

    def signature_items(self, config_params: dict | None) -> TransportRequestItems:
        return (
            (MessageFields.CONFIG_PARAMS, config_params),
            (MessageFields.CONFIG_CODE, self.config_code),
        )


@dataclass(frozen=True, slots=True)
class ZMQExecutionRequestPayload:
    """Normalized execution request fields used by server execution phases."""

    identity: ZMQExecutionIdentity
    pipeline_code: str
    config_transport: ZMQExecutionConfigTransport
    compile_control: ZMQExecutionCompileControl
    client_address: str | None = None

    @classmethod
    def from_execute_request(
        cls,
        request: ExecuteRequest,
    ) -> "ZMQExecutionRequestPayload":
        return cls(
            identity=ZMQExecutionIdentity(
                subject_id=request.subject_id,
                execution_subject_id=request.execution_subject_id,
                selected_pipeline_path=request.selected_pipeline_path,
            ),
            pipeline_code=request.pipeline_code,
            config_transport=ZMQExecutionConfigTransport.from_execute_request(request),
            compile_control=ZMQExecutionCompileControl.from_execute_request(request),
            client_address=request.client_address,
        )

    @property
    def subject_id(self) -> str:
        return self.identity.subject_id

    @property
    def execution_subject_id(self) -> str | None:
        return self.identity.execution_subject_id

    @property
    def selected_pipeline_path(self) -> str | None:
        return self.identity.selected_pipeline_path

    @property
    def config_params(self) -> dict | None:
        return self.config_transport.config_params

    @property
    def config_code(self) -> str | None:
        return self.config_transport.config_code

    @property
    def compile_only(self) -> bool:
        return self.compile_control.compile_only

    @property
    def compile_artifact_id(self) -> str | None:
        return self.compile_control.compile_artifact_id

    @property
    def request_signature(self) -> str:
        return self.signature_for_config_params(self.config_params)

    @property
    def compilation_signature(self) -> str:
        return self.signature_for_config_params(
            ZMQAuxiliaryExecutionParams.compilation_config_params(self.config_params)
        )

    @property
    def debug_replay_signature(self) -> str:
        from openhcs.core.debug import DebugExecutionConfig

        return self.signature_for_config_params(
            DebugExecutionConfig.compatibility_config_params(
                ZMQAuxiliaryExecutionParams.compilation_config_params(
                    self.config_params
                )
            )
        )

    @property
    def pipeline_sha(self) -> str:
        return hashlib.sha256(self.pipeline_code.encode("utf-8")).hexdigest()[:12]

    def signature_for_config_params(self, config_params: dict | None) -> str:
        payload = dict(
            self.identity.signature_items()
            + ((MessageFields.PIPELINE_CODE, self.pipeline_code),)
            + self.config_transport.signature_items(config_params)
        )
        canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
        return hashlib.sha256(canonical.encode("utf-8")).hexdigest()
