"""Typed request signatures for ZMQ execution and debug replay."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING, Any

from zmqruntime.messages import ExecuteRequest, MessageFields

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.orchestrator.execution_result import RuntimeObservationMode

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
EXECUTION_PLATE_ID_FIELD = "execution_plate_id"
SELECTED_PIPELINE_PATH_FIELD = "selected_pipeline_path"


class ZMQAuxiliaryParamField(Enum):
    """Transport keys consumed as typed auxiliary execution inputs."""

    WELL_FILTER = "well_filter"
    RUNTIME_OBSERVATION_EXPORT_PATH = "runtime_observation_export_path"


@dataclass(frozen=True, slots=True)
class ZMQAuxiliaryExecutionParams:
    """Auxiliary execution options shared by the ordinary client and server."""

    axis_filter: tuple[str, ...] | None = None
    debug_execution_config: DebugExecutionConfig | None = None
    runtime_observation_export_path: Path | None = None

    def runtime_observation_mode_for(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> RuntimeObservationMode:
        """Resolve retention from compiled needs plus an explicit export request."""

        return RuntimeObservationMode.from_parent_requirement(
            execution_bundle.requires_parent_runtime_observation
        ).including_parent_requirement(self.runtime_observation_export_path is not None)

    def to_transport(self) -> dict[str, Any]:
        """Project explicitly requested options into zmqruntime config_params."""

        params: dict[str, Any] = {}
        if self.axis_filter is not None:
            params[ZMQAuxiliaryParamField.WELL_FILTER.value] = list(self.axis_filter)
        if self.debug_execution_config is not None:
            params.update(self.debug_execution_config.to_config_params())
        if self.runtime_observation_export_path is not None:
            params[ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value] = str(
                self.runtime_observation_export_path
            )
        return params

    @classmethod
    def from_transport(
        cls,
        config_params: Mapping[str, Any] | None,
    ) -> ZMQAuxiliaryExecutionParams:
        if not config_params:
            return cls()
        return cls(
            axis_filter=cls._axis_filter_from_transport(
                config_params.get(ZMQAuxiliaryParamField.WELL_FILTER.value)
            ),
            debug_execution_config=cls._debug_config_from_transport(config_params),
            runtime_observation_export_path=cls._path_from_transport(
                config_params.get(
                    ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value
                )
            ),
        )

    @staticmethod
    def _axis_filter_from_transport(
        axis_filter: list[str] | tuple[str, ...] | str | int | None,
    ) -> tuple[str, ...] | None:
        if axis_filter is None:
            return None
        if isinstance(axis_filter, list):
            return tuple(str(axis_id) for axis_id in axis_filter)
        if isinstance(axis_filter, tuple):
            return tuple(str(axis_id) for axis_id in axis_filter)
        raise TypeError(
            "ZMQ config_params well_filter must be a concrete axis-id sequence, "
            f"got {type(axis_filter).__name__}."
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
    plate_pipeline: PipelineConfig


@dataclass(frozen=True, slots=True)
class ZMQExecutionIdentity:
    """Plate and source-selection identity shared by client and server."""

    plate_id: str
    execution_plate_id: str | None = None
    selected_pipeline_path: str | None = None

    def request_items(self) -> TransportRequestItems:
        items: list[tuple[str, TransportValue]] = [
            (MessageFields.PLATE_ID, self.plate_id),
        ]
        if self.execution_plate_id is not None:
            items.append((EXECUTION_PLATE_ID_FIELD, self.execution_plate_id))
        if self.selected_pipeline_path is not None:
            items.append((SELECTED_PIPELINE_PATH_FIELD, self.selected_pipeline_path))
        return tuple(items)

    def signature_items(self) -> TransportRequestItems:
        return (
            (MessageFields.PLATE_ID, self.plate_id),
            (EXECUTION_PLATE_ID_FIELD, self.execution_plate_id),
            (SELECTED_PIPELINE_PATH_FIELD, self.selected_pipeline_path),
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

    def request_items(self) -> TransportRequestItems:
        items: list[tuple[str, TransportValue]] = []
        if self.compile_only:
            items.append((MessageFields.COMPILE_ONLY, True))
        if self.compile_artifact_id is not None:
            items.append((MessageFields.COMPILE_ARTIFACT_ID, self.compile_artifact_id))
        return tuple(items)


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
                plate_id=request.plate_id,
                execution_plate_id=request.execution_plate_id,
                selected_pipeline_path=request.selected_pipeline_path,
            ),
            pipeline_code=request.pipeline_code,
            config_transport=ZMQExecutionConfigTransport.from_execute_request(request),
            compile_control=ZMQExecutionCompileControl.from_execute_request(request),
            client_address=request.client_address,
        )

    @property
    def plate_id(self) -> str:
        return self.identity.plate_id

    @property
    def execution_plate_id(self) -> str | None:
        return self.identity.execution_plate_id

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
    def debug_replay_signature(self) -> str:
        from openhcs.core.debug import DebugExecutionConfig

        return self.signature_for_config_params(
            DebugExecutionConfig.compatibility_config_params(self.config_params)
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
