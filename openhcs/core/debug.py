"""Typed debug/test-mode substrate for OpenHCS runtime execution."""

from __future__ import annotations

import json
import hashlib
import shutil
import time
import traceback
import threading
from abc import ABC, abstractmethod
from dataclasses import dataclass, field, replace
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable, ClassVar, Mapping, Self
from uuid import uuid4

from metaclass_registry import AutoRegisterMeta
from python_introspect import dataclass_from_mapping, project_dataclass, to_jsonable
from zmqruntime.messages import ResponseType, TypedWireMessage, WireView
import numpy as np

from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ArtifactPlan,
    ArtifactSpecRef,
    ArtifactType,
    MeasurementsArtifactType,
    RelationshipsArtifactType,
)
from openhcs.core.debug_view_models import DebugViewModel
from openhcs.core.function_patterns import CompiledFunctionInvocation
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisProjector,
    RuntimePlaneAxisValueProjection,
    RuntimePlaneProjection,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValueSet
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
)
from openhcs.core.runtime_array_values import RuntimeArrayPayload
from openhcs.core.progress import (
    ProgressContextPayload,
    ProgressEvent,
    ProgressExecutionContext,
    ProgressStatus,
    emit_event,
)
from openhcs.core.progress.types import (
    ErrorProgressStatus,
    PatternGroupProgressPhase,
    StartedProgressStatus,
    SuccessProgressStatus,
)
from openhcs.core.vfs_protocol import FileManagerLike

if TYPE_CHECKING:
    from openhcs.core.pipeline.compiler import CompiledRuntimeEnvironmentPlan
    from openhcs.core.runtime_stores import RuntimeValueStore


class DebugCommandType(ABC, metaclass=AutoRegisterMeta):
    """One user-facing debug/test-mode command; each command is a subclass.

    ``name`` is the command's wire spelling. A command owns what it does to a
    paused persistent worker.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugCommandType"]]] = {}

    name: ClassVar[str | None] = None

    @classmethod
    def apply_to_worker(cls, controller: "DebugPausedWorkerController") -> None:
        """Leave the worker paused at its current boundary."""

        controller.pause()


class AdvancesOneDebugBoundary:
    """Trait for debug commands that release exactly one boundary."""

    @classmethod
    def apply_to_worker(cls, controller: "DebugPausedWorkerController") -> None:
        controller.release_one_boundary()


class ToggleDebugCommand(DebugCommandType):
    name = "toggle"


class StepDebugCommand(AdvancesOneDebugBoundary, DebugCommandType):
    name = "step"


class RunDebugCommand(DebugCommandType):
    name = "run"

    @classmethod
    def apply_to_worker(cls, controller: "DebugPausedWorkerController") -> None:
        controller.run_continuously()


class RunToPauseDebugCommand(AdvancesOneDebugBoundary, DebugCommandType):
    name = "run_to_pause"


class RestartDebugCommand(AdvancesOneDebugBoundary, DebugCommandType):
    name = "restart"


class ChooseSourceGroupDebugCommand(DebugCommandType):
    name = "choose_source_group"


class RandomSourceGroupDebugCommand(DebugCommandType):
    name = "random_source_group"


class StopDebugCommand(DebugCommandType):
    name = "stop"

    @classmethod
    def apply_to_worker(cls, controller: "DebugPausedWorkerController") -> None:
        controller.stop()


class DebugBoundary(ABC, metaclass=AutoRegisterMeta):
    """Which runtime boundary a debug event reports; each boundary is a subclass.

    ``name`` is the boundary's wire spelling.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugBoundary"]]] = {}

    name: ClassVar[str | None] = None
    progress_status: ClassVar[type[ProgressStatus]]
    reports_output_artifacts: ClassVar[bool] = False
    carries_exception: ClassVar[bool] = False


class ReportsOutputArtifactsDebugBoundary:
    """Trait for boundaries that report the artifacts the invocation produced."""

    reports_output_artifacts: ClassVar[bool] = True


class BeforeInvocationDebugBoundary(DebugBoundary):
    name = "before_invocation"
    progress_status = StartedProgressStatus


class AfterInvocationDebugBoundary(ReportsOutputArtifactsDebugBoundary, DebugBoundary):
    name = "after_invocation"
    progress_status = SuccessProgressStatus


class ExceptionDebugBoundary(ReportsOutputArtifactsDebugBoundary, DebugBoundary):
    name = "exception"
    progress_status = ErrorProgressStatus
    carries_exception = True


class DebugWorkerState(ABC, metaclass=AutoRegisterMeta):
    """Where one persistent debug worker stands; each state is a subclass."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugWorkerState"]]] = {}

    name: ClassVar[str | None] = None


class RunningDebugWorker(DebugWorkerState):
    name = "running"


class PausedDebugWorker(DebugWorkerState):
    name = "paused"


class StoppedDebugWorker(DebugWorkerState):
    name = "stopped"


@dataclass(frozen=True, slots=True)
class DebugPausedWorkerStatus:
    """Status of a paused persistent debug worker."""

    debug_session_id: str
    state: type[DebugWorkerState]
    cursor: DebugCursor | None = None

    @classmethod
    def from_controller(
        cls,
        controller: "DebugPausedWorkerController",
    ) -> "DebugPausedWorkerStatus":
        return cls(
            debug_session_id=controller.debug_session_id,
            state=controller._state,
            cursor=controller._cursor,
        )


class DebugReplayMode(ABC, metaclass=AutoRegisterMeta):
    """How a debug replay reuses prepared execution state; each mode is a subclass."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugReplayMode"]]] = {}

    name: ClassVar[str | None] = None
    retains_compile_artifact: ClassVar[bool] = True
    keeps_worker_paused: ClassVar[bool] = False
    """The worker stays alive between commands, paused at invocation boundaries."""


class ColdReplay(DebugReplayMode):
    name = "cold"
    retains_compile_artifact = False


class WarmArtifactReplay(DebugReplayMode):
    name = "warm_artifact"


class PersistentPausedWorkerReplay(DebugReplayMode):
    name = "persistent_paused_worker"
    keeps_worker_paused = True


@dataclass(frozen=True, slots=True)
class DebugCommand:
    """Typed GUI command for a debug/test-mode session."""

    command_type: type[DebugCommandType]
    debug_session_id: str | None = None


@dataclass(frozen=True, slots=True)
class DebugCursor:
    """Invocation-aware debug cursor."""

    step_index: int
    step_scope_id: str | None
    group_key: str | None
    invocation_key: str | None
    pattern_group_identity: str | None = None

    @classmethod
    def from_invocation(
        cls,
        *,
        step_index: int,
        step_scope_id: str | None,
        invocation: CompiledFunctionInvocation,
        pattern_group_identity: str | None = None,
    ) -> "DebugCursor":
        return cls(
            step_index=step_index,
            step_scope_id=step_scope_id,
            group_key=invocation.key.group_key,
            invocation_key=DebugCursor.invocation_key_text(invocation),
            pattern_group_identity=pattern_group_identity,
        )

    @staticmethod
    def invocation_key_text(invocation: CompiledFunctionInvocation) -> str:
        key = invocation.key
        return f"{key.group_key}:{key.position}:{key.function_name}"

    @staticmethod
    def invocation_key_parts_text(
        *,
        group_key: str,
        position: int,
        function_name: str,
    ) -> str:
        return f"{group_key}:{position}:{function_name}"

    def matches_invocation_key_parts(
        self,
        *,
        group_key: str,
        position: int,
        function_name: str,
    ) -> bool:
        if self.invocation_key is None:
            return False
        return (
            self.group_key == group_key
            and self.invocation_key
            == self.invocation_key_parts_text(
                group_key=group_key,
                position=position,
                function_name=function_name,
            )
        )


@dataclass(frozen=True, slots=True)
class DebugArtifactRef:
    """Reference to a debug artifact or preview payload."""

    kind: type[ArtifactType]
    name: str
    cursor: DebugCursor
    storage_ref: str
    storage_backend: str | None = None
    preview_ref: str | None = None
    shape: tuple[int, ...] | None = None
    dtype: str | None = None
    identity: "DebugArtifactIdentity | None" = None
    content_digest: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "kind", ArtifactType.coerce(self.kind))
        if not self.name:
            raise ValueError("DebugArtifactRef.name cannot be empty.")
        if not self.storage_ref:
            raise ValueError("DebugArtifactRef.storage_ref cannot be empty.")

    @classmethod
    def from_artifact_plan(
        cls,
        *,
        plan: ArtifactPlan,
        cursor: DebugCursor,
    ) -> "DebugArtifactRef":
        """Build a metadata-only debug reference from a compiled artifact plan."""

        return cls(
            kind=plan.artifact_type,
            name=plan.name,
            cursor=cursor,
            storage_ref=plan.path,
            storage_backend="memory",
            identity=DebugArtifactIdentity.from_artifact_plan(plan),
        )

    @classmethod
    def from_bound_artifact(
        cls,
        *,
        plan: ArtifactPlan,
        cursor: DebugCursor,
        value: object,
    ) -> "DebugArtifactRef":
        """Build a reference carrying shape facts from one bound artifact value."""

        shape: tuple[int, ...] | None = None
        dtype: str | None = None
        if isinstance(value, RuntimeArrayPayload):
            shape = tuple(int(axis_size) for axis_size in value.shape)
            payload_data = value.array_payload_data()
            if isinstance(payload_data, np.ndarray):
                dtype = str(payload_data.dtype)
        elif isinstance(value, np.ndarray):
            shape = tuple(int(axis_size) for axis_size in value.shape)
            dtype = str(value.dtype)
        return replace(
            cls.from_artifact_plan(plan=plan, cursor=cursor),
            shape=shape,
            dtype=dtype,
        )

    def with_content_digest(self, digest: str | None) -> "DebugArtifactRef":
        return replace(self, content_digest=digest)


@dataclass(frozen=True, slots=True)
class DebugArtifactIdentity:
    """Stable logical identity for matching debug artifacts across replay runs."""

    name: str
    kind: type[ArtifactType]
    group_keys: tuple[str | None, ...] = (None,)
    producer_step_index: str | None = None
    producer_step_scope_id: str | None = None
    producer_step_name: str | None = None
    settings_digest: str | None = None

    @classmethod
    def from_artifact_plan(cls, plan: ArtifactPlan) -> "DebugArtifactIdentity":
        output_plan = plan if isinstance(plan, ArtifactOutputPlan) else None
        return cls(
            name=plan.name,
            kind=plan.artifact_type,
            group_keys=tuple(plan.group_keys or (None,)),
            producer_step_index=(
                None
                if output_plan is None or output_plan.producer_step_index is None
                else str(output_plan.producer_step_index)
            ),
            producer_step_scope_id=(
                None if output_plan is None else output_plan.producer_step_scope_id
            ),
            producer_step_name=(
                None if output_plan is None else output_plan.producer_step_name
            ),
            settings_digest=cls.settings_digest_for_plan(plan),
        )

    def matches(self, other: "DebugArtifactIdentity") -> bool:
        return (
            self.name == other.name
            and self.kind is other.kind
            and self.group_keys == other.group_keys
            and self.producer_step_index == other.producer_step_index
            and self.producer_step_scope_id == other.producer_step_scope_id
            and self.producer_step_name == other.producer_step_name
            and self.settings_digest == other.settings_digest
        )

    @staticmethod
    def settings_digest_for_plan(plan: ArtifactPlan) -> str | None:
        if not isinstance(plan, ArtifactOutputPlan):
            return None
        materialization = plan.materialization
        if materialization is None:
            return None
        payload = json.dumps(
            {
                "materialization": repr(materialization),
            },
            sort_keys=True,
        )
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()

@dataclass(frozen=True, slots=True)
class DebugArtifactRefProjection:
    """Typed debug projection over compiled artifact plans."""

    refs: tuple[DebugArtifactRef, ...] = ()

    @classmethod
    def from_artifact_plans(
        cls,
        *,
        artifact_plans: Mapping[ArtifactSpecRef, ArtifactPlan],
        cursor: DebugCursor,
        artifact_values: Mapping[ArtifactSpecRef, object] | None = None,
    ) -> "DebugArtifactRefProjection":
        ArtifactPlan.require_exact_map(
            artifact_plans,
            boundary="Debug artifact plan",
        )
        values = {} if artifact_values is None else artifact_values
        for ref in values:
            if not isinstance(ref, ArtifactSpecRef):
                raise TypeError(
                    "Debug artifact value maps require ArtifactSpecRef keys, "
                    f"got {type(ref).__name__}."
                )
        unknown_value_refs = tuple(ref for ref in values if ref not in artifact_plans)
        if unknown_value_refs:
            raise ValueError(
                "Debug artifact values require selected exact plans; missing plans "
                f"for {unknown_value_refs!r}."
            )
        return cls(
            refs=tuple(
                (
                    DebugArtifactRef.from_bound_artifact(
                        plan=plan,
                        cursor=cursor,
                        value=values[plan.ref()],
                    )
                    if plan.ref() in values
                    else DebugArtifactRef.from_artifact_plan(
                        plan=plan,
                        cursor=cursor,
                    )
                )
                for plan in artifact_plans.values()
            )
        )

    def of_artifact_type(
        self,
        artifact_type: type[ArtifactType],
    ) -> tuple[DebugArtifactRef, ...]:
        resolved_artifact_type = ArtifactType.coerce(artifact_type)
        return tuple(ref for ref in self.refs if ref.kind is resolved_artifact_type)

    @property
    def measurement_refs(self) -> tuple[DebugArtifactRef, ...]:
        return self.of_artifact_type(MeasurementsArtifactType)

    @property
    def relationship_refs(self) -> tuple[DebugArtifactRef, ...]:
        return self.of_artifact_type(RelationshipsArtifactType)


@dataclass(frozen=True, slots=True)
class DebugInvocationParameter:
    """JSON-safe parameter projection for one compiled function invocation."""

    name: str
    value_repr: str

    @classmethod
    def from_value(
        cls,
        *,
        name: str,
        value: Any,
        plane_projector: RuntimePlaneAxisProjector | None = None,
    ) -> "DebugInvocationParameter":
        """Project one bound call value without materializing or repr-ing payloads."""

        value_type = f"{type(value).__module__}.{type(value).__qualname__}"
        facts: list[str] = []
        projection_facts: tuple[str, ...] = ()
        projection: RuntimePlaneAxisValueProjection | None = None

        if isinstance(value, ObjectLabelValue):
            domain = value.object_label_domain()
            facts.extend(
                (
                    f"representation={value.representation.value!r}",
                    f"domain_scope={domain.scope.value!r}",
                    f"declared_object_count={domain.declared_object_count!r}",
                    f"declared_object_id_count={len(domain.declared_object_ids)}",
                    "declared_object_plane_count="
                    f"{len(domain.declared_object_id_domains)}",
                    f"source_plane_count={value.source_provenance.source_plane_count}",
                    f"source_image_name_count={len(value.source_image_names)}",
                )
            )
            projection = value.declared_plane_projection()
            facts.extend(
                (
                    "declared_plane_axis="
                    f"{None if value.plane_axis is None else value.plane_axis.value!r}",
                    "declared_cardinality="
                    f"{None if projection is None else projection.axis_size!r}",
                )
            )
            if isinstance(value, RuntimeArrayPayload):
                facts.append(f"shape={value.shape!r}")
                label_data = value.array_payload_data()
                if isinstance(label_data, np.ndarray):
                    facts.append(f"dtype={str(label_data.dtype)!r}")
        elif isinstance(value, RuntimeArrayPayload):
            facts.append(f"shape={value.shape!r}")
            image_data = value.array_payload_data()
            if isinstance(image_data, np.ndarray):
                facts.append(f"dtype={str(image_data.dtype)!r}")
            metadata = value.metadata
            if metadata.has_values:
                facts.extend(
                    (
                        f"source_dtype={metadata.source_dtype!r}",
                        f"axes={metadata.axes!r}",
                        "source_plane_count="
                        f"{metadata.source_provenance.source_plane_count}",
                        "source_image_name_count="
                        f"{len(metadata.source_image_names)}",
                    )
                )
            if metadata.plane_axis is not None:
                payload_shape = tuple(int(axis_size) for axis_size in value.shape)
                if plane_projector is not None and (
                    metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
                    or not isinstance(plane_projector, RuntimePlaneProjection)
                ):
                    projection = RuntimePlaneAxisValueProjection.from_projector(
                        plane_projector,
                        metadata.plane_axis,
                        metadata.source_image_names,
                    )
                if projection is None:
                    facts.append(f"plane_axis={metadata.plane_axis.value!r}")
                facts.extend(
                    (
                        f"declared_plane_axis={metadata.plane_axis.value!r}",
                        f"declared_cardinality={payload_shape[0]}",
                    )
                )
            else:
                facts.extend(
                    (
                        "declared_plane_axis=None",
                        "declared_cardinality=None",
                    )
                )
        elif isinstance(value, np.ndarray):
            facts.extend(
                (
                    f"shape={value.shape!r}",
                    f"dtype={str(value.dtype)!r}",
                )
            )
        elif isinstance(value, RuntimeSliceAlignedValueSet):
            facts.extend(
                (
                    f"slice_count={value.slice_count}",
                    f"declared_cardinality={value.slice_count}",
                )
            )
        elif isinstance(value, RuntimePlaneAxisValueProjection):
            projection = value
            facts.append(f"declared_cardinality={value.axis_size}")
        elif isinstance(value, Enum):
            facts.append(f"member={value.name}")
        elif isinstance(value, str):
            facts.extend(
                (
                    f"value={value[:128]!r}",
                    f"length={len(value)}",
                )
            )
        elif value is None or isinstance(value, (int, float, bool)):
            facts.append(f"value={value!r}")
        elif isinstance(value, Mapping):
            facts.append(f"item_count={len(value)}")
        elif isinstance(value, (tuple, list, set, frozenset)):
            facts.append(f"item_count={len(value)}")

        if projection is not None:
            plane_coordinate = (
                "preserved"
                if projection.plane_index is None
                else str(projection.plane_index)
            )
            projection_facts = (
                f"plane_axis={projection.axis.value!r}",
                f"plane_index={plane_coordinate}",
                f"axis_size={projection.axis_size}",
                f"source_alias_count={len(projection.source_aliases)}",
            )
        facts = [*projection_facts, *facts]

        value_text = value_type if not facts else f"{value_type}({', '.join(facts)})"
        if len(value_text) > 512:
            value_text = f"{value_text[:509]}..."
        return cls(name=name, value_repr=value_text)

    @classmethod
    def from_kwargs(
        cls,
        kwargs: Mapping[str, Any],
        *,
        plane_projector: RuntimePlaneAxisProjector | None = None,
    ) -> tuple["DebugInvocationParameter", ...]:
        return tuple(
            cls.from_value(
                name=str(name),
                value=value,
                plane_projector=plane_projector,
            )
            for name, value in sorted(kwargs.items(), key=lambda item: str(item[0]))
        )

@dataclass(frozen=True, slots=True, kw_only=True)
class DebugBoundaryState(ABC, metaclass=AutoRegisterMeta):
    """Common cursor/artifact state shared by debug events and snapshots."""

    __registry_key__ = "boundary_kind"
    __skip_if_no_key__ = True
    boundary_kind: ClassVar[str | None] = None

    cursor: DebugCursor
    step_name: str
    callable_name: str | None = None
    axis_id: str | None = None
    input_artifact_refs: tuple[DebugArtifactRef, ...] = ()
    output_artifact_refs: tuple[DebugArtifactRef, ...] = ()
    preview_refs: tuple[DebugArtifactRef, ...] = ()
    measurement_refs: tuple[DebugArtifactRef, ...] = ()
    relationship_refs: tuple[DebugArtifactRef, ...] = ()
    timing_seconds: float | None = None
    exception: str | None = None
    invocation_parameters: tuple[DebugInvocationParameter, ...] = ()


@dataclass(frozen=True, slots=True)
class DebugSnapshot(DebugBoundaryState):
    """Snapshot metadata for one debug execution boundary."""

    boundary_kind: ClassVar[str] = "snapshot"

    snapshot_id: str
    source_paths: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class DebugControlReplyStatus(WireView):
    """The envelope every debug control reply carries beside its fields."""

    status: ResponseType
    error: str | None = None


@dataclass(frozen=True, slots=True)
class DebugControlResponse(WireView):
    """A successful debug control response: ``status: ok`` beside its fields."""

    def to_control_response(self) -> dict[str, Any]:
        return {"status": ResponseType.OK.value, **self.to_dict()}

    @classmethod
    def from_control_response(cls, payload: Mapping[str, Any]) -> Self:
        reply = DebugControlReplyStatus.from_dict(payload)
        if reply.status is not ResponseType.OK:
            raise RuntimeError(reply.error or str(dict(payload)))
        return cls.from_dict(payload)


@dataclass(frozen=True, slots=True, kw_only=True)
class DebugSessionRequest(ABC):
    """Base request carrying a non-empty debug session id."""

    debug_session_id: str

    def __post_init__(self) -> None:
        self.validate_required_non_empty_values()

    @property
    def required_non_empty_values(self) -> tuple[tuple[str, str | None], ...]:
        return (("debug_session_id", self.debug_session_id),)

    def validate_required_non_empty_values(self) -> None:
        for field_name, value in self.required_non_empty_values:
            if not value:
                raise ValueError(f"{field_name} cannot be empty.")


@dataclass(frozen=True, slots=True)
class DebugSnapshotReadRequest(DebugSessionRequest, TypedWireMessage):
    """Control-channel request for reading one debug snapshot from the server."""

    wire_type: ClassVar[str] = "openhcs_debug_read_snapshot"

    snapshot_id: str
    snapshot_store_ref: str
    snapshot_store_backend: str | None = None

    @property
    def required_non_empty_values(self) -> tuple[tuple[str, str | None], ...]:
        return (
            ("debug_session_id", self.debug_session_id),
            ("snapshot_id", self.snapshot_id),
            ("snapshot_store_ref", self.snapshot_store_ref),
        )


@dataclass(frozen=True, slots=True)
class DebugSnapshotReadResponse(DebugControlResponse):
    """Control-channel response carrying snapshot metadata only."""

    snapshot: DebugSnapshot


@dataclass(frozen=True, slots=True)
class DebugArtifactExportRequest(DebugSessionRequest, TypedWireMessage):
    """Control-channel request for server-side artifact export/materialization."""

    wire_type: ClassVar[str] = "openhcs_debug_export_artifact"

    artifact_ref: DebugArtifactRef
    export_root: str
    snapshot_store_ref: str | None = None
    snapshot_store_backend: str | None = None

    @property
    def required_non_empty_values(self) -> tuple[tuple[str, str | None], ...]:
        return (
            ("debug_session_id", self.debug_session_id),
            ("export_root", self.export_root),
        )


@dataclass(frozen=True, slots=True)
class DebugArtifactExportResponse(DebugControlResponse):
    """Control-channel response containing the server-side export path."""

    exported_ref: str


@dataclass(frozen=True, slots=True)
class DebugRuntimeInspectionRequest(DebugSessionRequest, TypedWireMessage):
    """Control-channel request for a paused worker runtime inspection view."""

    wire_type: ClassVar[str] = "openhcs_debug_inspect_runtime"


@dataclass(frozen=True, slots=True)
class DebugRuntimeInspectionResponse(DebugControlResponse):
    """Control-channel response containing a renderer-independent debug view."""

    view_model: DebugViewModel


@dataclass(frozen=True, slots=True)
class DebugArtifactExportPlan:
    """Filesystem export plan executed in the worker/server namespace."""

    artifact_ref: DebugArtifactRef
    export_root: Path
    filemanager: FileManagerLike | None = None

    @property
    def source_path(self) -> Path:
        return Path(self.artifact_ref.preview_ref or self.artifact_ref.storage_ref)

    @property
    def destination_path(self) -> Path:
        suffix = self.source_path.suffix
        return self.export_root / f"{self.artifact_ref.name}{suffix}"

    def export(self) -> Path:
        if (
            self.artifact_ref.storage_backend is not None
            and self.filemanager is not None
        ):
            return self._export_vfs_payload()
        source_path = self.source_path
        if not source_path.exists():
            raise FileNotFoundError(
                f"Debug artifact source does not exist: {source_path}"
            )
        self.export_root.mkdir(parents=True, exist_ok=True)
        destination_path = self.destination_path
        if source_path.is_dir():
            shutil.copytree(source_path, destination_path, dirs_exist_ok=True)
        else:
            shutil.copy2(source_path, destination_path)
        return destination_path

    def _export_vfs_payload(self) -> Path:
        self.export_root.mkdir(parents=True, exist_ok=True)
        destination_path = self.destination_path
        payload = self.filemanager.load(
            self.artifact_ref.storage_ref,
            self.artifact_ref.storage_backend,
        )
        if isinstance(payload, bytes):
            destination_path.write_bytes(payload)
        elif isinstance(payload, str):
            destination_path.write_text(payload, encoding="utf-8")
        else:
            destination_path.write_text(
                json.dumps(payload, default=repr), encoding="utf-8"
            )
        return destination_path


@dataclass(frozen=True, slots=True)
class DebugWarmReplayArtifactAvailability:
    """Availability result for one warm-replay artifact output."""

    artifact_ref: DebugArtifactRef
    available: bool
    hydrated_from: str | None = None


@dataclass(frozen=True, slots=True)
class DebugWarmReplayArtifactReusePlan:
    """Nominal validation/hydration plan for skipped warm-replay outputs."""

    artifact_refs: tuple[DebugArtifactRef, ...]
    snapshot_store: "DebugSnapshotStore | None" = None

    @classmethod
    def from_artifact_plans(
        cls,
        *,
        artifact_plans: Mapping[ArtifactSpecRef, ArtifactPlan],
        cursor: DebugCursor,
        snapshot_store: "DebugSnapshotStore | None" = None,
    ) -> "DebugWarmReplayArtifactReusePlan":
        return cls(
            artifact_refs=DebugArtifactRefProjection.from_artifact_plans(
                artifact_plans=artifact_plans,
                cursor=cursor,
            ).refs,
            snapshot_store=snapshot_store,
        )

    def prepare(
        self, context: object
    ) -> tuple[DebugWarmReplayArtifactAvailability, ...]:
        hydration_context = DebugArtifactHydrationContext.from_execution_context(
            context
        )
        return tuple(
            self._prepare_ref(hydration_context, artifact_ref)
            for artifact_ref in self.artifact_refs
        )

    def require_available(self, context: object) -> None:
        results = self.prepare(context)
        missing = tuple(
            result.artifact_ref for result in results if not result.available
        )
        if missing:
            missing_text = ", ".join(
                f"{ref.kind.value}:{ref.name}@{ref.storage_ref}" for ref in missing
            )
            raise RuntimeError(
                "Warm debug replay cannot skip upstream step because expected "
                f"artifact outputs are unavailable: {missing_text}."
            )

    def _prepare_ref(
        self,
        hydration_context: "DebugArtifactHydrationContext",
        artifact_ref: DebugArtifactRef,
    ) -> DebugWarmReplayArtifactAvailability:
        if hydration_context.artifact_available(artifact_ref):
            return DebugWarmReplayArtifactAvailability(artifact_ref, available=True)
        source_ref = self._matching_snapshot_ref(artifact_ref)
        if source_ref is not None and hydration_context.hydrate(
            source_ref=source_ref,
            destination_ref=artifact_ref,
        ):
            return DebugWarmReplayArtifactAvailability(
                artifact_ref,
                available=True,
                hydrated_from=source_ref.storage_ref,
            )
        return DebugWarmReplayArtifactAvailability(artifact_ref, available=False)

    def _matching_snapshot_ref(
        self,
        artifact_ref: DebugArtifactRef,
    ) -> DebugArtifactRef | None:
        if self.snapshot_store is None or artifact_ref.identity is None:
            return None
        for snapshot_id in reversed(self.snapshot_store.list_snapshot_ids()):
            snapshot = self.snapshot_store.read_snapshot(snapshot_id)
            for candidate in snapshot.output_artifact_refs:
                if (
                    candidate.identity is not None
                    and artifact_ref.identity.matches(candidate.identity)
                    and candidate.storage_ref != artifact_ref.storage_ref
                ):
                    return candidate
        return None


@dataclass(frozen=True, slots=True)
class DebugArtifactHydrationContext:
    """Runtime storage context used to hydrate warm replay artifacts."""

    filemanager: FileManagerLike | None = None

    @classmethod
    def from_execution_context(
        cls,
        context: object,
    ) -> "DebugArtifactHydrationContext":
        if isinstance(context, DebugExecutionContext):
            return cls(filemanager=context.filemanager)
        return cls()

    def artifact_available(self, artifact_ref: DebugArtifactRef) -> bool:
        if artifact_ref.storage_backend is not None and self.filemanager is not None:
            try:
                return self.filemanager.exists(
                    artifact_ref.storage_ref,
                    artifact_ref.storage_backend,
                )
            except Exception:
                return False
        return Path(artifact_ref.storage_ref).exists()

    def content_digest(self, artifact_ref: DebugArtifactRef) -> str | None:
        if artifact_ref.storage_backend is not None and self.filemanager is not None:
            vfs_digest = self._vfs_content_digest(artifact_ref)
            if vfs_digest is not None:
                return vfs_digest
        return self._local_content_digest(artifact_ref.storage_ref)

    def content_matches(self, artifact_ref: DebugArtifactRef) -> bool:
        if artifact_ref.content_digest is None:
            return True
        return self.content_digest(artifact_ref) == artifact_ref.content_digest

    def snapshot_with_content_digests(
        self,
        snapshot: "DebugSnapshot",
    ) -> "DebugSnapshot":
        return DebugSnapshot(
            snapshot_id=snapshot.snapshot_id,
            cursor=snapshot.cursor,
            step_name=snapshot.step_name,
            callable_name=snapshot.callable_name,
            axis_id=snapshot.axis_id,
            source_paths=snapshot.source_paths,
            input_artifact_refs=tuple(
                self.ref_with_content_digest(ref)
                for ref in snapshot.input_artifact_refs
            ),
            output_artifact_refs=tuple(
                self.ref_with_content_digest(ref)
                for ref in snapshot.output_artifact_refs
            ),
            preview_refs=tuple(
                self.ref_with_content_digest(ref) for ref in snapshot.preview_refs
            ),
            measurement_refs=tuple(
                self.ref_with_content_digest(ref) for ref in snapshot.measurement_refs
            ),
            relationship_refs=tuple(
                self.ref_with_content_digest(ref) for ref in snapshot.relationship_refs
            ),
            timing_seconds=snapshot.timing_seconds,
            exception=snapshot.exception,
            invocation_parameters=snapshot.invocation_parameters,
        )

    def ref_with_content_digest(
        self,
        artifact_ref: DebugArtifactRef,
    ) -> DebugArtifactRef:
        if artifact_ref.content_digest is not None:
            return artifact_ref
        return artifact_ref.with_content_digest(self.content_digest(artifact_ref))

    def hydrate(
        self,
        *,
        source_ref: DebugArtifactRef,
        destination_ref: DebugArtifactRef,
    ) -> bool:
        if (
            source_ref.storage_backend is not None
            and destination_ref.storage_backend is not None
            and self.filemanager is not None
            and self.content_matches(source_ref)
            and self._hydrate_vfs_artifact(
                source_ref=source_ref,
                destination_ref=destination_ref,
            )
        ):
            return True
        if not self.content_matches(source_ref):
            return False
        return self._hydrate_local_artifact(
            source_ref=source_ref.storage_ref,
            destination_ref=destination_ref.storage_ref,
        )

    def _hydrate_vfs_artifact(
        self,
        *,
        source_ref: DebugArtifactRef,
        destination_ref: DebugArtifactRef,
    ) -> bool:
        if self.filemanager is None:
            return False
        if not self.filemanager.exists(
            source_ref.storage_ref, source_ref.storage_backend
        ):
            return False
        if self.filemanager.is_dir(source_ref.storage_ref, source_ref.storage_backend):
            return self._hydrate_vfs_directory(
                source_ref=source_ref,
                destination_ref=destination_ref,
            )
        payload = self.filemanager.load(
            source_ref.storage_ref,
            source_ref.storage_backend,
        )
        self.filemanager.save(
            payload,
            destination_ref.storage_ref,
            destination_ref.storage_backend,
        )
        return True

    def _hydrate_vfs_directory(
        self,
        *,
        source_ref: DebugArtifactRef,
        destination_ref: DebugArtifactRef,
    ) -> bool:
        if self.filemanager is None:
            return False
        self.filemanager.ensure_directory(
            destination_ref.storage_ref,
            destination_ref.storage_backend,
        )
        source_root = Path(source_ref.storage_ref)
        destination_root = Path(destination_ref.storage_ref)
        for source_file in self.filemanager.list_files(
            source_ref.storage_ref,
            source_ref.storage_backend,
            recursive=True,
        ):
            relative_path = Path(source_file).relative_to(source_root)
            payload = self.filemanager.load(source_file, source_ref.storage_backend)
            self.filemanager.save(
                payload,
                destination_root / relative_path,
                destination_ref.storage_backend,
            )
        return True

    @staticmethod
    def _hydrate_local_artifact(
        *,
        source_ref: str,
        destination_ref: str,
    ) -> bool:
        source_path = Path(source_ref)
        if not source_path.exists():
            return False
        destination_path = Path(destination_ref)
        destination_path.parent.mkdir(parents=True, exist_ok=True)
        if source_path.is_dir():
            shutil.copytree(source_path, destination_path, dirs_exist_ok=True)
        else:
            shutil.copy2(source_path, destination_path)
        return True

    def _vfs_content_digest(self, artifact_ref: DebugArtifactRef) -> str | None:
        if self.filemanager is None or artifact_ref.storage_backend is None:
            return None
        if not self.filemanager.exists(
            artifact_ref.storage_ref, artifact_ref.storage_backend
        ):
            return None
        if self.filemanager.is_dir(
            artifact_ref.storage_ref, artifact_ref.storage_backend
        ):
            source_root = Path(artifact_ref.storage_ref)
            digest = hashlib.sha256()
            for source_file in self.filemanager.list_files(
                artifact_ref.storage_ref,
                artifact_ref.storage_backend,
                recursive=True,
            ):
                relative_path = str(Path(source_file).relative_to(source_root))
                digest.update(relative_path.encode("utf-8"))
                payload = self.filemanager.load(
                    source_file, artifact_ref.storage_backend
                )
                digest.update(self._payload_digest_bytes(payload))
            return digest.hexdigest()
        payload = self.filemanager.load(
            artifact_ref.storage_ref,
            artifact_ref.storage_backend,
        )
        return hashlib.sha256(self._payload_digest_bytes(payload)).hexdigest()

    @staticmethod
    def _local_content_digest(storage_ref: str) -> str | None:
        path = Path(storage_ref)
        if not path.exists():
            return None
        if path.is_dir():
            digest = hashlib.sha256()
            for child in sorted(path.rglob("*")):
                if not child.is_file():
                    continue
                digest.update(str(child.relative_to(path)).encode("utf-8"))
                digest.update(child.read_bytes())
            return digest.hexdigest()
        return hashlib.sha256(path.read_bytes()).hexdigest()

    @staticmethod
    def _payload_digest_bytes(payload: object) -> bytes:
        if isinstance(payload, bytes):
            return payload
        if isinstance(payload, str):
            return payload.encode("utf-8")
        return json.dumps(payload, sort_keys=True, default=repr).encode("utf-8")


@dataclass(frozen=True, slots=True)
class DebugWorkerCommandRequest(DebugSessionRequest, TypedWireMessage):
    """Control-channel request for a persistent paused debug worker."""

    wire_type: ClassVar[str] = "openhcs_debug_worker_command"

    command_type: type[DebugCommandType]


@dataclass(frozen=True, slots=True)
class DebugWorkerCommandResponse(DebugControlResponse):
    """Control-channel response for a persistent debug-worker command."""

    worker: DebugPausedWorkerStatus


@dataclass(frozen=True, slots=True)
class DebugEvent(DebugBoundaryState):
    """Lightweight debug event emitted from runtime boundaries."""

    boundary_kind: ClassVar[str] = "event"

    event_type: type[DebugBoundary]
    traceback_text: str | None = None
    timestamp: float = field(default_factory=time.time)

    @classmethod
    def for_invocation(
        cls,
        *,
        event_type: type[DebugBoundary],
        cursor: DebugCursor,
        step_name: str,
        callable_name: str | None,
        axis_id: str | None,
        input_artifacts: DebugArtifactRefProjection,
        output_artifacts: DebugArtifactRefProjection = DebugArtifactRefProjection(),
        exception: BaseException | None = None,
        timing_seconds: float | None = None,
        invocation_parameters: tuple[DebugInvocationParameter, ...] = (),
    ) -> "DebugEvent":
        if event_type.carries_exception != (exception is not None):
            raise ValueError(
                f"{event_type.name!r} debug events "
                f"{'require' if event_type.carries_exception else 'cannot carry'} "
                "an exception."
            )
        reported_output_artifacts = (
            output_artifacts.refs if event_type.reports_output_artifacts else ()
        )
        event_ref_projection = (
            output_artifacts if event_type.reports_output_artifacts else input_artifacts
        )
        exception_text = None
        traceback_text = None
        if exception is not None:
            exception_text = f"{type(exception).__name__}: {exception}"
            traceback_text = traceback.format_exc()
        return cls(
            event_type=event_type,
            cursor=cursor,
            step_name=step_name,
            callable_name=callable_name,
            axis_id=axis_id,
            input_artifact_refs=input_artifacts.refs,
            output_artifact_refs=reported_output_artifacts,
            measurement_refs=event_ref_projection.measurement_refs,
            relationship_refs=event_ref_projection.relationship_refs,
            timing_seconds=timing_seconds,
            exception=exception_text,
            traceback_text=traceback_text,
            invocation_parameters=invocation_parameters,
        )

    def to_snapshot(self, *, snapshot_id: str) -> DebugSnapshot:
        """Build a metadata-only snapshot for this runtime event."""

        return project_dataclass(DebugSnapshot, self, snapshot_id=snapshot_id)


@dataclass(frozen=True, slots=True)
class DebugProgressContext(ProgressContextPayload):
    """Small debug context intended for ProgressEvent.context transport."""

    context_key: ClassVar[str] = "debug"

    debug_session_id: str
    snapshot_id: str | None
    cursor: DebugCursor
    event_type: type[DebugBoundary]
    snapshot_store_ref: str | None = None
    snapshot_store_backend: str | None = None

    @classmethod
    def from_event(
        cls,
        *,
        debug_session_id: str,
        event: DebugEvent,
        snapshot_id: str | None = None,
        snapshot_store_ref: str | None = None,
        snapshot_store_backend: str | None = None,
    ) -> "DebugProgressContext":
        if not debug_session_id:
            raise ValueError("debug_session_id cannot be empty.")
        return cls(
            debug_session_id=debug_session_id,
            snapshot_id=snapshot_id,
            cursor=event.cursor,
            event_type=event.event_type,
            snapshot_store_ref=snapshot_store_ref,
            snapshot_store_backend=snapshot_store_backend,
        )


@dataclass(frozen=True, slots=True)
class DebugProgressEventRequest(DebugSessionRequest):
    """Request for one lightweight ProgressEvent announcing debug state."""

    debug_event: DebugEvent
    progress_context: ProgressExecutionContext
    snapshot_id: str | None = None
    snapshot_store_ref: str | None = None
    snapshot_store_backend: str | None = None
    completed: int = 0
    total: int = 1
    percent: float = 0.0

    @property
    def required_non_empty_values(self) -> tuple[tuple[str, str | None], ...]:
        return (
            ("debug_session_id", self.debug_session_id),
            ("execution_id", self.progress_context.execution_id),
            ("subject_id", self.progress_context.subject_id),
        )

    def debug_progress_context(self) -> DebugProgressContext:
        return DebugProgressContext.from_event(
            debug_session_id=self.debug_session_id,
            event=self.debug_event,
            snapshot_id=self.snapshot_id,
            snapshot_store_ref=self.snapshot_store_ref,
            snapshot_store_backend=self.snapshot_store_backend,
        )

    def to_progress_event(self) -> ProgressEvent:
        if self.debug_event.axis_id is None:
            raise ValueError("DebugProgressEventRequest requires debug_event.axis_id.")
        return self.progress_context.event(
            axis_id=self.debug_event.axis_id,
            step_name=self.debug_event.step_name,
            phase=PatternGroupProgressPhase,
            status=self.debug_event.event_type.progress_status,
            percent=self.percent,
            completed=self.completed,
            total=self.total,
            message=self.debug_event.event_type.name,
            context=self.debug_progress_context().to_context(),
            error=self.debug_event.exception,
            traceback=self.debug_event.traceback_text,
        )


class DebugPausedWorkerController:
    """Thread-shared pause/resume controller for persistent debug replay."""

    def __init__(self, *, debug_session_id: str) -> None:
        if not debug_session_id:
            raise ValueError("debug_session_id cannot be empty.")
        self.debug_session_id = debug_session_id
        self._condition = threading.Condition()
        self._state = RunningDebugWorker
        self._cursor: DebugCursor | None = None
        self._context: DebugExecutionContext | None = None
        self._step_permits = 0
        self._continuous = False

    @property
    def status(self) -> DebugPausedWorkerStatus:
        with self._condition:
            return DebugPausedWorkerStatus.from_controller(self)

    def bind_context(self, context: "DebugExecutionContext") -> None:
        with self._condition:
            self._context = context

    def runtime_inspection_view(self) -> "DebugViewModel":
        with self._condition:
            if self._context is None:
                raise RuntimeError("Debug worker context is not available.")
            if self._state is not PausedDebugWorker:
                raise RuntimeError("Runtime inspection requires a paused debug worker.")
            from openhcs.core.debug_views import RuntimeValuesDebugViewSection

            return RuntimeValuesDebugViewSection.view_model_for_store(
                self._context.runtime_value_store,
                title=f"Runtime Values ({self.debug_session_id[:8]})",
            )

    def apply_command(
        self, command_type: type[DebugCommandType]
    ) -> DebugPausedWorkerStatus:
        with self._condition:
            command_type.apply_to_worker(self)
            return DebugPausedWorkerStatus.from_controller(self)

    def pause(self) -> None:
        self._state = PausedDebugWorker

    def stop(self) -> None:
        self._state = StoppedDebugWorker
        self._condition.notify_all()

    def run_continuously(self) -> None:
        self._continuous = True
        self._state = RunningDebugWorker
        self._condition.notify_all()

    def release_one_boundary(self) -> None:
        self._continuous = False
        self._step_permits += 1
        self._state = RunningDebugWorker
        self._condition.notify_all()

    def wait_at_boundary(self, event: DebugEvent) -> None:
        if event.event_type is not AfterInvocationDebugBoundary:
            return
        with self._condition:
            self._cursor = event.cursor
            if self._continuous:
                self._state = RunningDebugWorker
                return
            if self._step_permits > 0:
                self._step_permits -= 1
                self._state = RunningDebugWorker
                return
            self._state = PausedDebugWorker
            while self._state is PausedDebugWorker:
                self._condition.wait()
            if self._state is StoppedDebugWorker:
                raise DebugWorkerStopped("Persistent debug worker was stopped.")


class DebugWorkerStopped(RuntimeError):
    """Raised inside a persistent worker when the controller receives STOP."""


class DebugPausedWorkerRegistry:
    """Process-local registry for persistent debug worker controllers."""

    _controllers: ClassVar[dict[str, DebugPausedWorkerController]] = {}
    _lock: ClassVar[threading.Lock] = threading.Lock()

    @classmethod
    def controller_for(cls, debug_session_id: str) -> DebugPausedWorkerController:
        with cls._lock:
            controller = cls._controllers.get(debug_session_id)
            if controller is None:
                controller = DebugPausedWorkerController(
                    debug_session_id=debug_session_id
                )
                cls._controllers[debug_session_id] = controller
            return controller

    @classmethod
    def remove(cls, debug_session_id: str) -> None:
        with cls._lock:
            cls._controllers.pop(debug_session_id, None)


@dataclass(frozen=True, slots=True)
class DebugSession:
    """Controller identity for one short-lived debug/test-mode execution."""

    debug_session_id: str
    execution_id: str | None = None
    subject_id: str | None = None
    axis_id: str | None = None
    command_type: type[DebugCommandType] | None = None
    selected_source_group: str | None = None
    cursor: DebugCursor | None = None
    breakpoints: tuple[DebugCursor, ...] = ()
    snapshot_store_ref: str | None = None
    snapshot_store_backend: str | None = None
    dirty_from_cursor: DebugCursor | None = None

    @classmethod
    def create(
        cls,
        *,
        execution_id: str | None = None,
        subject_id: str | None = None,
        axis_id: str | None = None,
        command_type: type[DebugCommandType] | None = None,
    ) -> "DebugSession":
        return cls(
            debug_session_id=str(uuid4()),
            execution_id=execution_id,
            subject_id=subject_id,
            axis_id=axis_id,
            command_type=command_type,
        )

    def with_command(self, command_type: type[DebugCommandType]) -> "DebugSession":
        return replace(self, command_type=command_type)

    def with_snapshot_store(
        self,
        *,
        snapshot_store_ref: str | None,
        snapshot_store_backend: str | None,
        axis_id: str | None = None,
    ) -> "DebugSession":
        return replace(
            self,
            axis_id=self.axis_id if axis_id is None else axis_id,
            snapshot_store_ref=snapshot_store_ref,
            snapshot_store_backend=snapshot_store_backend,
        )

    def with_cursor(self, cursor: DebugCursor) -> "DebugSession":
        return replace(self, cursor=cursor)

    def mark_dirty_from_cursor(self) -> "DebugSession":
        if self.cursor is None:
            return self
        return replace(self, dirty_from_cursor=self.cursor)


@dataclass(frozen=True, slots=True)
class DebugTerminalSummary:
    """Terminal UI/debug summary for one completed debug session."""

    debug_session_id: str
    subject_id: str
    terminal_status: str
    cursor: DebugCursor | None = None
    command_type: type[DebugCommandType] | None = None
    axis_id: str | None = None
    snapshot_id: str | None = None
    snapshot_store_ref: str | None = None
    snapshot_store_backend: str | None = None
    step_name: str | None = None
    callable_name: str | None = None
    completed_at_unix: float | None = None

    @classmethod
    def from_session(
        cls,
        session: DebugSession,
        *,
        terminal_status: str,
        completed_at_unix: float | None = None,
    ) -> "DebugTerminalSummary":
        if session.subject_id is None:
            raise ValueError("DebugTerminalSummary requires session.subject_id.")
        return project_dataclass(
            cls,
            session,
            terminal_status=terminal_status,
            completed_at_unix=completed_at_unix,
        )

    def with_snapshot(
        self,
        *,
        snapshot: DebugSnapshot | None,
        snapshot_id: str | None,
        snapshot_store_ref: str | None,
        snapshot_store_backend: str | None,
    ) -> "DebugTerminalSummary":
        summary = replace(
            self,
            snapshot_id=snapshot_id,
            snapshot_store_ref=snapshot_store_ref,
            snapshot_store_backend=snapshot_store_backend,
        )
        if snapshot is None:
            return summary
        return replace(
            summary,
            cursor=snapshot.cursor,
            axis_id=snapshot.axis_id,
            step_name=snapshot.step_name,
            callable_name=snapshot.callable_name,
        )


@dataclass(slots=True)
class DebugExecutionConfig:
    """Serializable debug execution settings carried by existing run requests."""

    CONFIG_PARAMS_KEY: ClassVar[str] = "debug_execution"

    debug_session_id: str
    snapshot_store_ref: str | None = None
    snapshot_store_backend: str | None = None
    command_type: type[DebugCommandType] = RunDebugCommand
    selected_source_group: str | None = None
    pause_step_indices: tuple[int, ...] = ()
    start_step_index: int = 0
    start_after_invocation_key: str | None = None
    replay_mode: type[DebugReplayMode] = ColdReplay

    def __post_init__(self) -> None:
        if not self.debug_session_id:
            raise ValueError("DebugExecutionConfig.debug_session_id cannot be empty.")
        if self.start_step_index < 0:
            raise ValueError("start_step_index cannot be negative.")

    def to_config_params(self) -> dict[str, Any]:
        return {self.CONFIG_PARAMS_KEY: to_jsonable(self)}

    def compile_cache_config_params(self) -> dict[str, Any]:
        """Return debug config params containing only compile-relevant state."""

        return replace(
            self,
            command_type=RunDebugCommand,
            start_step_index=0,
            start_after_invocation_key=None,
        ).to_config_params()

    @classmethod
    def compatibility_config_params(
        cls,
        config_params: Mapping[str, Any] | None,
    ) -> dict[str, Any] | None:
        """Normalize debug replay config for compile-artifact compatibility checks."""

        if not config_params:
            return None
        payload = config_params.get(cls.CONFIG_PARAMS_KEY)
        if payload is None:
            return dict(config_params)
        normalized = dict(config_params)
        normalized.update(cls.from_payload(payload).compile_cache_config_params())
        return normalized

    @classmethod
    def from_payload(cls, payload: Mapping[str, Any]) -> "DebugExecutionConfig":
        return dataclass_from_mapping(cls, payload)


class DebugInvocationExecutionStrategy(ABC, metaclass=AutoRegisterMeta):
    """Command-specific invocation execution window for bounded debug runs."""

    __registry_key__ = "command_type"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[type[DebugCommandType], type["DebugInvocationExecutionStrategy"]]
    ] = {}

    command_type: ClassVar[type[DebugCommandType] | None] = None

    def __init__(self, config: DebugExecutionConfig | None = None) -> None:
        self.config = config

    @classmethod
    def for_config(
        cls,
        config: DebugExecutionConfig,
    ) -> "DebugInvocationExecutionStrategy":
        strategy_type = cls.__registry__.get(
            config.command_type,
            NeverStopDebugInvocationExecutionStrategy,
        )
        return strategy_type(config)

    def should_skip_invocation(self, cursor: DebugCursor) -> bool:
        del cursor
        return False

    def should_stop_after_invocation(self, event: DebugEvent) -> bool:
        del event
        return False


class NeverStopDebugInvocationExecutionStrategy(DebugInvocationExecutionStrategy):
    """Default invocation strategy for commands that stop at step boundaries."""


class StepDebugInvocationExecutionStrategy(DebugInvocationExecutionStrategy):
    """Execute exactly one compiled invocation for the debug STEP command."""

    command_type = StepDebugCommand

    def __init__(self, config: DebugExecutionConfig | None = None) -> None:
        super().__init__(config)
        self._executed_invocations = 0
        self._waiting_for_start_after = bool(
            config and config.start_after_invocation_key
        )

    def should_skip_invocation(self, cursor: DebugCursor) -> bool:
        if self.config is None or not self._waiting_for_start_after:
            return False
        if cursor.invocation_key == self.config.start_after_invocation_key:
            self._waiting_for_start_after = False
        return True

    def should_stop_after_invocation(self, event: DebugEvent) -> bool:
        if event.event_type is not AfterInvocationDebugBoundary:
            return False
        self._executed_invocations += 1
        return self._executed_invocations >= 1


class DebugStepStopStrategy(ABC, metaclass=AutoRegisterMeta):
    """Command-specific policy for stopping bounded debug execution after a step."""

    __registry_key__ = "command_type"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[type[DebugCommandType], type["DebugStepStopStrategy"]]
    ] = {}

    command_type: ClassVar[type[DebugCommandType] | None] = None

    def __init__(self, config: DebugExecutionConfig | None = None) -> None:
        self.config = config

    @classmethod
    def for_config(
        cls,
        config: DebugExecutionConfig,
    ) -> "DebugStepStopStrategy":
        strategy_type = cls.__registry__.get(
            config.command_type,
            NeverStopDebugStepStrategy,
        )
        return strategy_type(config)

    @abstractmethod
    def should_stop_after_step(
        self,
        *,
        step_index: int,
        step_name: str,
    ) -> bool:
        """Return whether execution should stop after this completed step."""


class NeverStopDebugStepStrategy(DebugStepStopStrategy):
    """Default command strategy for unbounded debug run commands."""

    def should_stop_after_step(
        self,
        *,
        step_index: int,
        step_name: str,
    ) -> bool:
        del step_index, step_name
        return False


class StepDebugStepStopStrategy(DebugStepStopStrategy):
    """Stop after one completed step."""

    command_type = StepDebugCommand

    def should_stop_after_step(
        self,
        *,
        step_index: int,
        step_name: str,
    ) -> bool:
        del step_name
        if self.config is None:
            raise RuntimeError("Step debug strategy requires a config.")
        return step_index == self.config.start_step_index


class RunToPauseDebugStepStopStrategy(DebugStepStopStrategy):
    """Stop when a completed step is marked as a debug pause boundary."""

    command_type = RunToPauseDebugCommand

    def should_stop_after_step(
        self,
        *,
        step_index: int,
        step_name: str,
    ) -> bool:
        del step_name
        if self.config is None:
            raise RuntimeError("Run-to-pause debug strategy requires a config.")
        return step_index in self.config.pause_step_indices


class DebugExecutionPolicy(ABC, metaclass=AutoRegisterMeta):
    """Nominal policy for installing per-run debug behavior on contexts."""

    __registry_key__ = "policy_kind"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugExecutionPolicy"]]] = {}

    policy_kind: ClassVar[str | None] = None

    @classmethod
    def from_config_params(
        cls,
        config_params: Mapping[str, Any] | None,
    ) -> "DebugExecutionPolicy":
        payload = (
            None
            if not config_params
            else config_params.get(DebugExecutionConfig.CONFIG_PARAMS_KEY)
        )
        if payload is None:
            return NoOpDebugExecutionPolicy()
        return ProgressDebugExecutionPolicy(DebugExecutionConfig.from_payload(payload))

    @classmethod
    def from_config(
        cls,
        config: DebugExecutionConfig | None,
    ) -> "DebugExecutionPolicy":
        if config is None:
            return NoOpDebugExecutionPolicy()
        return ProgressDebugExecutionPolicy(config)

    @abstractmethod
    def install_context_sink(
        self,
        request: DebugSinkInstallRequest,
    ) -> None:
        """Install this policy's debug sink on a worker context."""

    def step_stop_strategy(self) -> DebugStepStopStrategy:
        """Return the command-specific step-stop strategy for this policy."""

        return NeverStopDebugStepStrategy()

    def should_execute_step(self, step_index: int) -> bool:
        """Return whether a pipeline step should execute for this debug run."""

        del step_index
        return True

    def should_reuse_step_outputs(self, step_index: int) -> bool:
        """Return whether skipped step outputs are expected to be materialized."""

        del step_index
        return False

    def prepare_reused_step_outputs(
        self,
        *,
        step_index: int,
        step_name: str,
        step_scope_id: str | None,
        context: object,
        artifact_outputs: Mapping[ArtifactSpecRef, ArtifactPlan],
    ) -> None:
        """Validate/hydrate outputs for a skipped warm-replay step."""

        del step_index, step_name, step_scope_id, context, artifact_outputs

    @abstractmethod
    def axis_filter_for_available(
        self,
        available_axis_ids: tuple[str, ...],
    ) -> list[str]:
        """Return the axis IDs this execution policy should compile/run."""

    def compile_worker_count(self, configured_num_workers: int) -> int:
        """Return the worker count the compiler should use for assignments."""

        return configured_num_workers

    def compiled_runtime_environment(
        self,
        runtime_environment: "CompiledRuntimeEnvironmentPlan",
    ) -> "CompiledRuntimeEnvironmentPlan":
        """Return the runtime environment plan selected by this policy."""

        return runtime_environment


class DebugExecutionContext(ABC):
    """Execution context owned by a running pipeline worker."""

    @property
    @abstractmethod
    def filemanager(self) -> FileManagerLike:
        """Return the FileManager used by the active execution context."""

    @property
    @abstractmethod
    def debug_event_sink(self) -> "DebugEventSink":
        """Return the debug sink installed for the active execution."""

    @abstractmethod
    def install_debug_event_sink(self, debug_event_sink: "DebugEventSink") -> None:
        """Install the debug sink selected for this execution context."""

    @property
    @abstractmethod
    def runtime_value_store(self) -> "RuntimeValueStore":
        """Return the RuntimeValueStore owned by the active execution context."""


@dataclass(frozen=True, slots=True)
class DebugSinkInstallRequest:
    """Execution identity needed to install one worker debug sink."""

    context: DebugExecutionContext
    progress_context: ProgressExecutionContext

    def __post_init__(self) -> None:
        if not isinstance(self.context, DebugExecutionContext):
            raise TypeError(
                "DebugSinkInstallRequest.context must implement DebugExecutionContext."
            )
        for field_name, value in (
            ("execution_id", self.progress_context.execution_id),
            ("subject_id", self.progress_context.subject_id),
        ):
            if not value:
                raise ValueError(f"{field_name} cannot be empty.")


class NoOpDebugExecutionPolicy(DebugExecutionPolicy):
    """Debug execution policy for normal non-debug runs."""

    policy_kind = "noop"

    def install_context_sink(
        self,
        request: DebugSinkInstallRequest,
    ) -> None:
        del request

    def axis_filter_for_available(
        self,
        available_axis_ids: tuple[str, ...],
    ) -> list[str]:
        return list(available_axis_ids)


@dataclass(frozen=True, slots=True)
class ProgressDebugExecutionPolicy(DebugExecutionPolicy):
    """Debug execution policy that emits runtime events as ProgressEvents."""

    policy_kind = "progress"

    config: DebugExecutionConfig

    def install_context_sink(
        self,
        request: DebugSinkInstallRequest,
    ) -> None:
        invocation_strategy = DebugInvocationExecutionStrategy.for_config(self.config)
        pause_controller = (
            DebugPausedWorkerRegistry.controller_for(self.config.debug_session_id)
            if self.config.replay_mode.keeps_worker_paused
            else None
        )
        if pause_controller is not None:
            pause_controller.bind_context(request.context)

        if self.config.snapshot_store_ref is not None:
            debug_event_sink: DebugEventSink = LocalSnapshotProgressDebugEventSink(
                debug_session_id=self.config.debug_session_id,
                progress_context=request.progress_context,
                emit_progress=emit_event,
                snapshot_store=self.snapshot_store_for_context(request.context),
                snapshot_store_ref=self.config.snapshot_store_ref,
                snapshot_store_backend=self.config.snapshot_store_backend,
                invocation_strategy=invocation_strategy,
                pause_controller=pause_controller,
            )
        else:
            debug_event_sink = ProgressDebugEventSink(
                debug_session_id=self.config.debug_session_id,
                progress_context=request.progress_context,
                emit_progress=emit_event,
                invocation_strategy=invocation_strategy,
                pause_controller=pause_controller,
            )
        request.context.install_debug_event_sink(debug_event_sink)

    def step_stop_strategy(self) -> DebugStepStopStrategy:
        return DebugStepStopStrategy.for_config(self.config)

    def should_execute_step(self, step_index: int) -> bool:
        return step_index >= self.config.start_step_index

    def should_reuse_step_outputs(self, step_index: int) -> bool:
        return (
            self.config.replay_mode.retains_compile_artifact
            and step_index < self.config.start_step_index
        )

    def prepare_reused_step_outputs(
        self,
        *,
        step_index: int,
        step_name: str,
        step_scope_id: str | None,
        context: object,
        artifact_outputs: Mapping[ArtifactSpecRef, ArtifactPlan],
    ) -> None:
        if not self.should_reuse_step_outputs(step_index):
            return
        snapshot_store = (
            self.snapshot_store_for_context(context)
            if self.config.snapshot_store_ref is not None
            else None
        )
        DebugWarmReplayArtifactReusePlan.from_artifact_plans(
            artifact_plans=artifact_outputs,
            cursor=DebugCursor(
                step_index=step_index,
                step_scope_id=step_scope_id,
                group_key=None,
                invocation_key=None,
            ),
            snapshot_store=snapshot_store,
        ).require_available(context)

    def axis_filter_for_available(
        self,
        available_axis_ids: tuple[str, ...],
    ) -> list[str]:
        if self.config.selected_source_group is not None:
            return [self.config.selected_source_group]
        return [] if not available_axis_ids else [available_axis_ids[0]]

    def compile_worker_count(self, configured_num_workers: int) -> int:
        if self.config.replay_mode.keeps_worker_paused:
            return 1
        return configured_num_workers

    def compiled_runtime_environment(
        self,
        runtime_environment: "CompiledRuntimeEnvironmentPlan",
    ) -> "CompiledRuntimeEnvironmentPlan":
        if not self.config.replay_mode.keeps_worker_paused:
            return runtime_environment
        return runtime_environment.with_execution_shape(
            use_threading=True,
            configured_num_workers=1,
        )

    def snapshot_store_for_context(
        self,
        context: DebugExecutionContext,
    ) -> "DebugSnapshotStore":
        if self.config.snapshot_store_ref is None:
            raise RuntimeError(
                "snapshot_store_ref is required for debug snapshot storage."
            )
        if self.config.snapshot_store_backend is None:
            return LocalDebugSnapshotStore(
                root_path=Path(self.config.snapshot_store_ref),
                debug_session_id=self.config.debug_session_id,
            )
        return FileManagerDebugSnapshotStore(
            filemanager=context.filemanager,
            backend=self.config.snapshot_store_backend,
            root_path=self.config.snapshot_store_ref,
            debug_session_id=self.config.debug_session_id,
        )


class DebugEventSink(metaclass=AutoRegisterMeta):
    """Runtime sink for debug/test-mode events."""

    __registry_key__ = "sink_kind"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugEventSink"]]] = {}

    sink_kind: ClassVar[str | None] = None

    @classmethod
    def registered_types(cls) -> tuple[type["DebugEventSink"], ...]:
        return tuple(cls.__registry__.values())

    def record(self, event: DebugEvent) -> None:
        """Record one debug event."""

    def captures_invocation_events(self) -> bool:
        """Return whether invocation debug events need to be constructed."""
        return True

    def should_skip_invocation(self, cursor: DebugCursor) -> bool:
        del cursor
        return False

    def should_stop_after_invocation(self, event: DebugEvent) -> bool:
        del event
        return False


class NoOpDebugEventSink(DebugEventSink):
    """Default sink used by production execution."""

    sink_kind = "noop"

    def captures_invocation_events(self) -> bool:
        return False

    def record(self, event: DebugEvent) -> None:
        del event


class RecordingDebugEventSink(DebugEventSink):
    """In-memory sink for tests and local diagnostics."""

    sink_kind = "recording"

    def __init__(self) -> None:
        self.events: list[DebugEvent] = []

    def record(self, event: DebugEvent) -> None:
        self.events.append(event)


class ProgressDebugEventSink(DebugEventSink):
    """Debug sink that emits lightweight ProgressEvent records."""

    sink_kind = "progress"

    def __init__(
        self,
        *,
        debug_session_id: str,
        progress_context: ProgressExecutionContext,
        emit_progress: Callable[[ProgressEvent], None],
        snapshot_store_ref: str | None = None,
        snapshot_store_backend: str | None = None,
        invocation_strategy: DebugInvocationExecutionStrategy | None = None,
        pause_controller: DebugPausedWorkerController | None = None,
    ) -> None:
        if not debug_session_id:
            raise ValueError("debug_session_id cannot be empty.")
        self.debug_session_id = debug_session_id
        self.progress_context = progress_context
        self.emit_progress = emit_progress
        self.snapshot_store_ref = snapshot_store_ref
        self.snapshot_store_backend = snapshot_store_backend
        self.invocation_strategy = (
            invocation_strategy or NeverStopDebugInvocationExecutionStrategy()
        )
        self.pause_controller = pause_controller

    def record(self, event: DebugEvent) -> None:
        self.emit_progress(
            DebugProgressEventRequest(
                debug_session_id=self.debug_session_id,
                debug_event=event,
                progress_context=self.progress_context,
                snapshot_store_ref=self.snapshot_store_ref,
                snapshot_store_backend=self.snapshot_store_backend,
            ).to_progress_event()
        )
        if self.pause_controller is not None:
            self.pause_controller.wait_at_boundary(event)

    def should_skip_invocation(self, cursor: DebugCursor) -> bool:
        return self.invocation_strategy.should_skip_invocation(cursor)

    def should_stop_after_invocation(self, event: DebugEvent) -> bool:
        return self.invocation_strategy.should_stop_after_invocation(event)


class LocalSnapshotProgressDebugEventSink(DebugEventSink):
    """Debug sink that writes local snapshots and emits lightweight progress."""

    sink_kind = "local_snapshot_progress"

    def __init__(
        self,
        *,
        debug_session_id: str,
        progress_context: ProgressExecutionContext,
        emit_progress: Callable[[ProgressEvent], None],
        snapshot_store: "DebugSnapshotStore",
        snapshot_store_ref: str,
        snapshot_store_backend: str | None = None,
        invocation_strategy: DebugInvocationExecutionStrategy | None = None,
        pause_controller: DebugPausedWorkerController | None = None,
    ) -> None:
        if snapshot_store.debug_session_id != debug_session_id:
            raise ValueError(
                "snapshot_store.debug_session_id must match debug_session_id."
            )
        self.debug_session_id = debug_session_id
        self.progress_context = progress_context
        self.emit_progress = emit_progress
        self.snapshot_store = snapshot_store
        self.snapshot_store_ref = snapshot_store_ref
        self.snapshot_store_backend = snapshot_store_backend
        self.invocation_strategy = (
            invocation_strategy or NeverStopDebugInvocationExecutionStrategy()
        )
        self.pause_controller = pause_controller

    def record(self, event: DebugEvent) -> None:
        snapshot_id = str(uuid4())
        self.snapshot_store.write_snapshot(event.to_snapshot(snapshot_id=snapshot_id))
        self.emit_progress(
            DebugProgressEventRequest(
                debug_session_id=self.debug_session_id,
                debug_event=event,
                progress_context=self.progress_context,
                snapshot_id=snapshot_id,
                snapshot_store_ref=self.snapshot_store_ref,
                snapshot_store_backend=self.snapshot_store_backend,
            ).to_progress_event()
        )
        if self.pause_controller is not None:
            self.pause_controller.wait_at_boundary(event)

    def should_skip_invocation(self, cursor: DebugCursor) -> bool:
        return self.invocation_strategy.should_skip_invocation(cursor)

    def should_stop_after_invocation(self, event: DebugEvent) -> bool:
        return self.invocation_strategy.should_stop_after_invocation(event)


@dataclass(frozen=True, slots=True)
class DebugStoreManifest:
    """The snapshots one debug session's store holds."""

    debug_session_id: str
    snapshot_ids: tuple[str, ...] = ()


class DebugSnapshotStore(ABC, metaclass=AutoRegisterMeta):
    """Store abstraction for debug snapshot metadata."""

    __registry_key__ = "store_kind"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugSnapshotStore"]]] = {}

    store_kind: ClassVar[str | None] = None
    debug_session_id: str

    @classmethod
    def registered_types(cls) -> tuple[type["DebugSnapshotStore"], ...]:
        return tuple(cls.__registry__.values())

    @abstractmethod
    def write_snapshot(self, snapshot: DebugSnapshot) -> object:
        """Write one snapshot and return the concrete storage reference."""

    @abstractmethod
    def read_snapshot(self, snapshot_id: str) -> DebugSnapshot:
        """Read one snapshot by ID."""

    @abstractmethod
    def list_snapshot_ids(self) -> tuple[str, ...]:
        """List snapshot IDs available in this store."""

    def manifest(self) -> DebugStoreManifest:
        return DebugStoreManifest(
            debug_session_id=self.debug_session_id,
            snapshot_ids=tuple(sorted(self.list_snapshot_ids())),
        )

    @abstractmethod
    def write_manifest(self) -> object:
        """Persist the current manifest and return the concrete storage reference."""


@dataclass(slots=True)
class LocalDebugSnapshotStore(DebugSnapshotStore):
    """Local filesystem-backed debug snapshot metadata store."""

    store_kind = "local"

    root_path: Path
    debug_session_id: str

    def __post_init__(self) -> None:
        self.root_path = Path(self.root_path)

    @classmethod
    def for_session(
        cls,
        *,
        root_path: str | Path,
        session: DebugSession,
    ) -> "LocalDebugSnapshotStore":
        return cls(root_path=Path(root_path), debug_session_id=session.debug_session_id)

    @property
    def session_path(self) -> Path:
        return self.root_path / self.debug_session_id

    @property
    def manifest_path(self) -> Path:
        return self.session_path / "manifest.json"

    def snapshot_path(self, snapshot_id: str) -> Path:
        if not snapshot_id:
            raise ValueError("snapshot_id cannot be empty.")
        return self.session_path / f"{snapshot_id}.json"

    def write_snapshot(self, snapshot: DebugSnapshot) -> Path:
        snapshot = DebugArtifactHydrationContext().snapshot_with_content_digests(
            snapshot
        )
        self.session_path.mkdir(parents=True, exist_ok=True)
        path = self.snapshot_path(snapshot.snapshot_id)
        path.write_text(
            json.dumps(to_jsonable(snapshot), indent=2, sort_keys=True),
            encoding="utf-8",
        )
        self.write_manifest()
        return path

    def read_snapshot(self, snapshot_id: str) -> DebugSnapshot:
        return dataclass_from_mapping(
            DebugSnapshot,
            json.loads(self.snapshot_path(snapshot_id).read_text(encoding="utf-8")),
        )

    def list_snapshot_ids(self) -> tuple[str, ...]:
        if not self.session_path.exists():
            return ()
        return tuple(
            path.stem
            for path in sorted(self.session_path.glob("*.json"))
            if path.name != self.manifest_path.name
        )

    def write_manifest(self) -> Path:
        self.session_path.mkdir(parents=True, exist_ok=True)
        self.manifest_path.write_text(
            json.dumps(to_jsonable(self.manifest()), indent=2, sort_keys=True),
            encoding="utf-8",
        )
        return self.manifest_path


@dataclass(frozen=True, slots=True)
class FileManagerDebugSnapshotStore(DebugSnapshotStore):
    """FileManager/VFS-backed debug snapshot metadata store."""

    store_kind = "filemanager"

    filemanager: FileManagerLike
    backend: str
    root_path: str | Path
    debug_session_id: str

    @property
    def session_path(self) -> str:
        return str(Path(self.root_path) / self.debug_session_id)

    @property
    def manifest_path(self) -> str:
        return str(Path(self.session_path) / "manifest.json")

    def snapshot_path(self, snapshot_id: str) -> str:
        if not snapshot_id:
            raise ValueError("snapshot_id cannot be empty.")
        return str(Path(self.session_path) / f"{snapshot_id}.json")

    def write_snapshot(self, snapshot: DebugSnapshot) -> str:
        snapshot = DebugArtifactHydrationContext(
            filemanager=self.filemanager,
        ).snapshot_with_content_digests(snapshot)
        self.filemanager.ensure_directory(self.session_path, self.backend)
        path = self.snapshot_path(snapshot.snapshot_id)
        self.filemanager.save(to_jsonable(snapshot), path, self.backend)
        self.write_manifest()
        return path

    def read_snapshot(self, snapshot_id: str) -> DebugSnapshot:
        payload = self.filemanager.load(
            self.snapshot_path(snapshot_id),
            self.backend,
        )
        if isinstance(payload, str):
            payload = json.loads(payload)
        return dataclass_from_mapping(DebugSnapshot, payload)

    def list_snapshot_ids(self) -> tuple[str, ...]:
        if not self.filemanager.exists(self.session_path, self.backend):
            return ()
        return tuple(
            Path(path).stem
            for path in sorted(
                str(path)
                for path in self.filemanager.list_files(
                    self.session_path,
                    self.backend,
                    recursive=False,
                )
            )
            if Path(path).name != "manifest.json"
        )

    def write_manifest(self) -> str:
        self.filemanager.ensure_directory(self.session_path, self.backend)
        self.filemanager.save(
            to_jsonable(self.manifest()),
            self.manifest_path,
            self.backend,
        )
        return self.manifest_path


NO_OP_DEBUG_EVENT_SINK = NoOpDebugEventSink()


def debug_event_sink_from_context(context: DebugExecutionContext) -> DebugEventSink:
    if not isinstance(context, DebugExecutionContext):
        raise TypeError(
            "Function runtime context must implement DebugExecutionContext."
        )
    sink = context.debug_event_sink
    if not isinstance(sink, DebugEventSink):
        raise TypeError(
            "ProcessingContext.debug_event_sink must be DebugEventSink, "
            f"got {type(sink).__name__}."
        )
    return sink


def is_debug_export(name: str, value: object) -> bool:
    return (
        isinstance(value, type)
        and value.__module__ == __name__
        and not name.startswith("_")
    ) or name in {"NO_OP_DEBUG_EVENT_SINK", "debug_event_sink_from_context"}


__all__ = tuple(
    name for name, value in globals().items() if is_debug_export(name, value)
)
