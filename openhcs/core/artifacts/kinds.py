"""The artifact kind family: what each kind of artifact payload means.

A kind validates, names, contextualizes, composes and materializes its payloads.
It never switches on a payload's type: each payload answers through its own
methods (``contextualized_output``, ``stored_slices``, ``match_alignment``), and
a kind with one nominal payload type declares it once.
"""

from __future__ import annotations
from openhcs.core.runtime_plane_projection import RuntimeSlicePlaneAxis

from abc import ABC, abstractmethod
from collections.abc import Sequence
from pathlib import Path
from typing import TYPE_CHECKING, ClassVar, cast

from metaclass_registry import AutoRegisterMeta

from openhcs.core.artifacts.payloads import (
    AnyPayloadShape,
    ArrayPayloadShape,
    MappingPayloadShape,
    NamedArtifactPayload,
    PayloadShape,
    TablePayloadShape,
)
from openhcs.core.axes import AxisFamily
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.memory import detect_memory_type
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_alignment import (
    RuntimeSliceAlignedValues,
    RuntimeSliceAlignedValueSet,
)

if TYPE_CHECKING:
    from openhcs.core.artifact_key_selection import AdapterRecordedArtifactOutputPolicy
    from openhcs.core.artifacts.plans import ArtifactOutputPlan, OutputTarget
    from openhcs.core.artifacts.sidecars import ArtifactSidecarRole
    from openhcs.core.artifacts.specs import ArtifactSpec
    from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
    from openhcs.core.measurement_dialect import MeasurementDialect
    from openhcs.core.projected_image_output import SourceProjectedImageOutput
    from openhcs.core.runtime_artifact_values import RuntimeValue
    from openhcs.core.runtime_image_values import ImagePayload, ImagePayloadMetadata
    from openhcs.core.runtime_measurements import MeasurementSubject, MeasurementTable
    from openhcs.core.runtime_plane_projection import RuntimePlaneAxisProjector
    from openhcs.core.runtime_spatial_grid import SpatialGrid
    from openhcs.core.runtime_stores import StoredRuntimeValue
    from openhcs.core.runtime_tabular_values import ColumnarRows
    from openhcs.core.source_image_provenance import SourceImageProvenance
    from openhcs.core.source_projection import OpenHCSPlaneAddress


class ArtifactType(ABC, metaclass=AutoRegisterMeta):
    """Registered runtime artifact payload category."""

    __registry_key__ = "value"
    __skip_if_no_key__ = True

    value: ClassVar[str]
    payload_shape: ClassVar[type[PayloadShape]] = AnyPayloadShape
    participates_in_measurement_source_names: ClassVar[bool] = False
    participates_in_main_flow_output: ClassVar[bool] = False
    carries_source_image_context: ClassVar[bool] = False

    @classmethod
    def runtime_parameter_types(cls) -> tuple[type, ...]:
        """Return nominal payload types accepted by callable artifact parameters."""

        return ()

    @classmethod
    def accepts_parameter_annotation(cls, annotation: object) -> bool:
        """Return whether an annotation accepts this artifact's runtime payload."""

        from openhcs.core.pipeline.function_contracts import (
            annotation_accepts_runtime_type,
        )

        return any(
            annotation_accepts_runtime_type(annotation, runtime_type)
            for runtime_type in cls.runtime_parameter_types()
        )

    @classmethod
    def coerce(cls, artifact_type: ArtifactTypeValue) -> type[ArtifactType]:
        """Return the registered artifact type for a class or wire value."""
        if isinstance(artifact_type, str):
            try:
                return cls.__registry__[artifact_type]
            except KeyError as exc:
                raise ValueError(f"Unknown artifact type {artifact_type!r}.") from exc
        if isinstance(artifact_type, type) and issubclass(artifact_type, cls):
            return artifact_type
        raise TypeError(
            "Artifact type must be an ArtifactType class or registered value, "
            f"got {type(artifact_type).__name__}."
        )

    @classmethod
    def require_registered(
        cls,
        artifact_type: ArtifactTypeValue,
        field_name: str,
    ) -> type[ArtifactType]:
        """Return one registered kind for a declaration field, or fail."""

        resolved = cls.coerce(artifact_type)
        if resolved not in ArtifactType.__registry__.values():
            raise ValueError(
                f"{field_name} is not a registered ArtifactType: {resolved.__name__}."
            )
        return resolved

    @classmethod
    def description(cls) -> str:
        return f"{cls.payload_shape.name} {cls.value} payload"

    @classmethod
    def diagnostic_label(cls) -> str:
        """Return the stable artifact type label used in diagnostics."""
        return f"<{cls.__name__}: {cls.value!r}>"

    @classmethod
    def validate_output_declaration(cls, spec: ArtifactSpec) -> None:
        """Validate common kind invariants regardless of payload recording owner."""

        del spec

    @classmethod
    def validate_native_output_declaration(cls, spec: ArtifactSpec) -> None:
        """Validate kind requirements for native returned payloads."""

        del spec

    @classmethod
    def validate_recorded_output_declaration(
        cls,
        spec: ArtifactSpec,
        policy: type[AdapterRecordedArtifactOutputPolicy],
    ) -> None:
        """Validate kind requirements for declaration-owned adapter recording."""

        del spec, policy

    @classmethod
    def normalize_group_scoped_payload(
        cls,
        output_plan: ArtifactOutputPlan,
        value: object,
    ) -> object:
        """Normalize payload axes already represented by compiled group scope."""

        del output_plan
        return value

    @classmethod
    def uses_aggregate_materialization_identity(cls, data: object) -> bool:
        """Return whether one payload must be named as a semantic aggregate."""

        del data
        return False

    @classmethod
    def projected_materialization_base_path(
        cls,
        *,
        artifact_name: str,
        aggregate_filename: str,
        analysis_output_dir: str | Path,
        image_output_dir: str | Path,
    ) -> Path:
        """Return the writer-neutral base for projected source-plane outputs."""

        del artifact_name, image_output_dir
        return Path(analysis_output_dir) / aggregate_filename

    @classmethod
    def materialization_base_path(
        cls,
        *,
        descriptor_filename: str,
        source_filename: str | None,
        uses_source_identity_filename: bool,
        analysis_output_dir: str | Path,
        image_output_dir: str | Path,
    ) -> Path:
        """Return the persistent base path for one scalar artifact output."""

        del source_filename, uses_source_identity_filename, image_output_dir
        return Path(analysis_output_dir) / descriptor_filename

    @classmethod
    def retained_filename_qualifier(cls, artifact_name: str) -> str | None:
        """Retain families whose existing paths already own artifact identity."""
        return None

    # -- contextualizing a returned value -------------------------------------
    #
    # ``contextualize_output`` asks the returned value which of the four hooks
    # below applies to it (``contextualized_output`` on the payload family);
    # every hook defaults to keeping the value as returned.

    @classmethod
    def owned_output(cls, output_value: object) -> object:
        """Return a function's returned value as this kind receives it."""
        return output_value

    @classmethod
    def contextualize_output(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        """Give one returned value the source context ``target`` declares."""

        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        return RuntimeSliceProjection.contextualized_output(
            cls,
            cls.owned_output(output_value),
            source_payload,
            target,
            plane_projection,
        )

    @classmethod
    def contextualize_value(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        """Contextualize one value that carries no image or slice alignment."""
        del source_payload, target, plane_projection
        return output_value

    @classmethod
    def contextualize_image(
        cls,
        source_payload: object,
        output_value: ImagePayload,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        """Contextualize one returned image payload."""
        return cls.contextualize_value(
            source_payload, output_value, target, plane_projection
        )

    @classmethod
    def contextualize_projected_image(
        cls,
        source_payload: object,
        output_value: SourceProjectedImageOutput,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        """Contextualize a result that declares its own source transformation."""
        return cls.contextualize_value(
            source_payload, output_value, target, plane_projection
        )

    @classmethod
    def contextualize_aligned(
        cls,
        source_payload: object,
        output_value: RuntimeSliceAlignedValueSet,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        """Contextualize one returned value per runtime slice."""
        return cls.contextualize_value(
            source_payload, output_value, target, plane_projection
        )

    @classmethod
    def contextualize_output_from_projector(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projector: RuntimePlaneAxisProjector | None,
    ) -> object:
        """Keep context-free artifacts outside image-axis projection."""
        del source_payload, target, plane_projector
        return output_value

    @classmethod
    def output_owns_source_context(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> bool:
        """Return whether a returned value already carries its source context."""
        del source_payload, output_value, target, plane_projection
        return False

    @classmethod
    def contextualize_projected_output(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projector: RuntimePlaneAxisProjector | None,
    ) -> object:
        """Resolve plane projection only after the artifact strategy is selected."""

        from openhcs.core.runtime_image_values import (
            owned_runtime_value,
            preserve_declared_image_payload_axis,
        )

        output_value = owned_runtime_value(output_value)
        plane_projection = (
            None
            if plane_projector is None
            else preserve_declared_image_payload_axis(
                plane_projector,
                output_value,
                source_payload=source_payload,
            )
        )
        if plane_projection is None and target.variable_components:
            if plane_projector is None:
                if cls.output_owns_source_context(
                    source_payload, output_value, target, None
                ):
                    return output_value
                raise ValueError(
                    f"Artifact output {target.describe()} preserves variable "
                    f"components {target.variable_components!r} but the "
                    "runtime invocation supplies no plane projector."
                )
            plane_projection = RuntimePlaneAxisValueProjection.require_from_projector(
                plane_projector,
                RuntimeSlicePlaneAxis,
            )
        return cls.contextualize_output(
            source_payload,
            output_value,
            target,
            plane_projection,
        )

    # -- runtime payload validation and normalization -------------------------

    @classmethod
    def normalize_runtime_payload(
        cls,
        name: str,
        value: object,
    ) -> object:
        """Convert one raw return into this artifact type's nominal payload."""

        del name
        return value

    @classmethod
    def normalize_source_payload(
        cls,
        data: object,
        channel_axis: int | None,
    ) -> tuple[object, int | None]:
        """Normalize source pixels according to this artifact's payload semantics."""

        return data, channel_axis

    @classmethod
    def source_image_payload_from_runtime_value(cls, value: object) -> object | None:
        """Read image context from this artifact's currently resolved payload."""
        return None

    @classmethod
    def compose_runtime_values(
        cls,
        values: Sequence[RuntimeValue],
        producer_group_scope: ComponentGroupScope | None = None,
    ) -> object:
        """Compose producer records according to this artifact's semantics."""

        del producer_group_scope
        if len(values) != 1:
            raise ValueError(
                f"{cls.__name__} does not define grouped runtime composition for "
                f"{len(values)} values."
            )
        return values[0].data

    @classmethod
    def normalize_slice_aligned_value(
        cls,
        value: RuntimeSliceAlignedValueSet[object],
        output_plan: ArtifactOutputPlan,
        *,
        axis_id: str,
    ) -> object:
        """Keep one returned payload per runtime slice."""

        del output_plan, axis_id
        return value

    @classmethod
    def accepts_runtime_payload(cls, data: object) -> bool:
        """Return whether data satisfies this artifact's nominal payload contract."""

        return cls.payload_shape.accepts(data)

    @classmethod
    def validate_runtime_payload(
        cls,
        name: str,
        data: object,
    ) -> None:
        """Validate one nominal payload, or each payload it stores per slice."""

        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        members = RuntimeSliceProjection.stored_slices(data)
        invalid = tuple(
            type(member).__name__
            for member in members
            if not cls.accepts_runtime_payload(member)
        )
        if invalid:
            raise TypeError(
                f"Artifact {name!r} expected {cls.description()}, "
                f"got {', '.join(invalid)}."
            )
        if isinstance(data, NamedArtifactPayload):
            data.validate_artifact_name(name)

    @classmethod
    def materialization_payload(cls, value: RuntimeValue) -> object:
        """Return the payload exposed to materializers for this artifact type."""
        return value.data

    @classmethod
    def materialization_image_metadata(cls, value: RuntimeValue) -> ImagePayloadMetadata:
        """Return the image metadata this kind's payload carries for naming."""
        from openhcs.core.runtime_image_values import ImagePayloadMetadata

        del value
        return ImagePayloadMetadata()

    @classmethod
    def runtime_semantic_id(cls, data: object) -> str | None:
        """Return artifact-owned subidentity for one nominal runtime value."""

        del data
        return None

    @classmethod
    def publishes_to_main_flow(
        cls,
        sidecar_role: type[ArtifactSidecarRole] | None,
    ) -> bool:
        """Return whether this artifact role participates in the main image flow."""

        return cls.participates_in_main_flow_output and sidecar_role is None

    @classmethod
    def reduce_materialization_records(
        cls,
        *,
        records: tuple[StoredRuntimeValue, ...],
        output_plan: ArtifactOutputPlan,
    ) -> tuple[StoredRuntimeValue, ...]:
        """Reduce records across every compiled group of one artifact output."""

        del output_plan
        return records

    @classmethod
    def reduce_materialization_scopes(
        cls,
        *,
        records: tuple[StoredRuntimeValue, ...],
        output_plan: ArtifactOutputPlan,
        group_key: str | None,
    ) -> tuple[StoredRuntimeValue, ...]:
        """Partition records by exact scope before artifact-specific reduction."""

        records_by_scope: dict[
            RuntimeExecutionAxisScope,
            list[StoredRuntimeValue],
        ] = {}
        for record in records:
            records_by_scope.setdefault(record.key.scope, []).append(record)
        return tuple(
            reduced_record
            for scoped_records in records_by_scope.values()
            for reduced_record in cls.reduce_materialization_scope(
                records=tuple(scoped_records),
                output_plan=output_plan,
                group_key=group_key,
            )
        )

    @classmethod
    def reduce_materialization_scope(
        cls,
        *,
        records: tuple[StoredRuntimeValue, ...],
        output_plan: ArtifactOutputPlan,
        group_key: str | None,
    ) -> tuple[StoredRuntimeValue, ...]:
        del output_plan, group_key
        if len(records) <= 1:
            return records
        record_locations = tuple(
            (
                record.key.semantic_id,
                record.location.path,
            )
            for record in records
        )
        raise RuntimeError(
            f"Ambiguous RuntimeValueStore records for planned artifact "
            f"materialization '{records[0].key.name}' "
            f"({records[0].key.artifact_type.value}) on axis "
            f"'{records[0].key.scope.axis_id}' group "
            f"{records[0].key.scope.value_text!r}: {record_locations!r}."
        )


ArtifactTypeValue = type[ArtifactType] | str


def artifact_type_strategy_key_from_class(name: str, cls: type[object]) -> str | None:
    """Return the nominal strategy key for a class declaring an ArtifactType member."""
    del name
    member = cls.__dict__.get("artifact_type")
    if isinstance(member, type) and issubclass(member, ArtifactType):
        return artifact_type_strategy_key(member)
    return None


def artifact_type_strategy_key(artifact_type: type[ArtifactType]) -> str:
    """Return the JSON-safe nominal key for an artifact-type strategy."""
    return f"{artifact_type.__module__}.{artifact_type.__qualname__}"


class ArtifactTypeStrategyMatchMixin:
    """MRO match hook for strategy roots selected by ArtifactType inheritance."""

    artifact_type: ClassVar[type[ArtifactType] | None] = None
    __key_extractor__ = staticmethod(artifact_type_strategy_key_from_class)

    def __init_subclass__(cls, **kwargs):
        super().__init_subclass__(**kwargs)
        key = artifact_type_strategy_key_from_class(cls.__name__, cls)
        if key is not None and cls.__dict__.get("strategy_key") is None:
            cls.strategy_key = key

    @classmethod
    def for_artifact_type(cls, artifact_type: ArtifactTypeValue):
        return cls.for_context(ArtifactType.coerce(artifact_type))

    def matches(self, context: type[ArtifactType]) -> bool:
        artifact_type = type(self).artifact_type
        return artifact_type is not None and issubclass(
            ArtifactType.coerce(context), artifact_type
        )


class NominalPayloadKind:
    """Capability of a kind whose payloads are instances of one nominal type."""

    @classmethod
    @abstractmethod
    def runtime_payload_type(cls) -> type:
        """Return the nominal type every payload of this kind is an instance of."""

    @classmethod
    def accepts_runtime_payload(cls, data: object) -> bool:
        return isinstance(data, cls.runtime_payload_type())


class SourceContextKind:
    """Capability of a kind whose payloads receive the source image's context."""

    carries_source_image_context: ClassVar[bool] = True

    @classmethod
    def contextualize_output_from_projector(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projector: RuntimePlaneAxisProjector | None,
    ) -> object:
        return cls.contextualize_projected_output(
            source_payload,
            output_value,
            target,
            plane_projector,
        )


class SpecialArtifactType(ArtifactType):
    """Generic artifact type for explicit side-channel payloads."""

    value = "special"


class ImagePayloadArtifactKind(SourceContextKind, ArtifactType):
    """Capability of kinds whose payloads are image payloads (images, labels)."""

    payload_shape = ArrayPayloadShape
    participates_in_main_flow_output = True

    @classmethod
    def owned_output(cls, output_value: object) -> object:
        from openhcs.core.runtime_image_values import owned_runtime_value

        return owned_runtime_value(output_value)

    @classmethod
    def source_image_payload_from_runtime_value(cls, value: object) -> object:
        return value

    @classmethod
    def materialization_image_metadata(cls, value: RuntimeValue) -> ImagePayloadMetadata:
        from openhcs.core.runtime_image_values import as_runtime_value

        return as_runtime_value(cls.materialization_payload(value)).image_metadata


class ImageArtifactType(ImagePayloadArtifactKind):
    """Image array artifact type."""

    value = "image"
    participates_in_measurement_source_names = True

    @classmethod
    def output_owns_source_context(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> bool:
        """Return whether an image result already carries complete source identity."""

        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        if not output_value.owns_complete_source_context(plane_projection):
            return False
        output_surfaces = RuntimeSliceProjection.output_slices(output_value)
        if not all(
            output_surface.metadata.has_complete_source_identity(output_surface)
            for output_surface in output_surfaces
        ):
            return False
        if target.requires_source_slice_identity:
            source_surfaces = RuntimeSliceProjection.output_slices(source_payload)
            return len(output_surfaces) == len(source_surfaces) and all(
                output_surface.metadata.source_provenance.represented_source_identities
                == source_surface.metadata.source_provenance.represented_source_identities
                for source_surface, output_surface in zip(
                    source_surfaces,
                    output_surfaces,
                    strict=True,
                )
            )
        return True

    @classmethod
    def contextualize_projected_image(
        cls,
        source_payload: object,
        output_value: SourceProjectedImageOutput,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        del target
        return output_value.resolve_source_context(source_payload, plane_projection)

    @classmethod
    def contextualize_aligned(
        cls,
        source_payload: object,
        output_value: RuntimeSliceAlignedValueSet,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        from openhcs.core.runtime_artifact_values import RuntimeValue
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        projection = RuntimePlaneAxisValueProjection.require_runtime_slice_axis(
            plane_projection,
            output_value.slice_count,
            value_name="Runtime-slice-aligned image output",
        )
        return output_value.map_indexed_slices(
            lambda slice_index, item: cls.contextualize_output(
                RuntimeSliceProjection.value_for_slice(
                    source_payload, projection.selected_plane(slice_index),
                ),
                RuntimeValue.payload_of(item),
                target,
                None,
            )
        )

    @classmethod
    def contextualize_image(
        cls,
        source_payload: object,
        output_value: ImagePayload,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        if (
            target.variable_components
            and plane_projection is not None
            and plane_projection.preserves_complete_axis
        ):
            output_value = output_value.with_undeclared_plane_axis(plane_projection)
        if target.collapses_runtime_slices():
            if output_value.declared_plane_axis is RuntimeSlicePlaneAxis:
                output_value = RuntimeSliceProjection.value_for_singleton_slice(
                    output_value,
                    source_description=f"Image output {target.describe()}",
                )
            if (
                RuntimeSliceProjection.declared_plane_axis(source_payload)
                is RuntimeSlicePlaneAxis
            ):
                source_ref = target.source_context_source()
                if source_ref is None:
                    raise ValueError(
                        f"Image output {target.describe()} consumes a runtime "
                        "stack without a declared source-context relation."
                    )
                collapsed_metadata = source_payload.metadata.collapse_leading_plane_axis()
                source_payload = collapsed_metadata.with_source_provenance(
                    collapsed_metadata.source_provenance.with_source_image_names(
                        (source_ref.name,)
                    )
                ).attach_source_context_to(output_value)
            plane_projection = None
        if cls.output_owns_source_context(
            source_payload,
            output_value,
            target,
            plane_projection,
        ) and not source_payload.requires_output_plane_contextualization(
            output_value,
            plane_projection,
        ):
            if output_value.keeps_own_source_context:
                return output_value
            return source_payload.fill_output_source_context(output_value)
        return source_payload.contextualize_image_output(output_value, plane_projection)

    @classmethod
    def retained_filename_qualifier(cls, artifact_name: str) -> str:
        """Distinguish named retained images sharing one physical source plane."""
        return artifact_name

    @classmethod
    def projected_materialization_base_path(
        cls,
        *,
        artifact_name: str,
        aggregate_filename: str,
        analysis_output_dir: str | Path,
        image_output_dir: str | Path,
    ) -> Path:
        """Place writer-projected image planes in the pipeline image output."""

        del aggregate_filename, analysis_output_dir
        return Path(image_output_dir) / artifact_name

    @classmethod
    def materialization_base_path(
        cls,
        *,
        descriptor_filename: str,
        source_filename: str | None,
        uses_source_identity_filename: bool,
        analysis_output_dir: str | Path,
        image_output_dir: str | Path,
    ) -> Path:
        """Place source-named scalar images in the pipeline image output."""

        if uses_source_identity_filename and source_filename is not None:
            return Path(image_output_dir) / source_filename
        return super().materialization_base_path(
            descriptor_filename=descriptor_filename,
            source_filename=source_filename,
            uses_source_identity_filename=uses_source_identity_filename,
            analysis_output_dir=analysis_output_dir,
            image_output_dir=image_output_dir,
        )

    @classmethod
    def runtime_parameter_types(cls) -> tuple[type, ...]:
        import numpy as np

        from openhcs.core.runtime_array_values import RuntimeArrayPayload

        return (np.ndarray, RuntimeArrayPayload)

    @classmethod
    def normalize_runtime_payload(
        cls,
        name: str,
        value: object,
    ) -> object:
        """Apply the declared image identity without discarding payload context."""

        from openhcs.core.runtime_image_values import owned_runtime_value

        def named_payload(payload: object) -> object:
            metadata = payload.metadata
            return metadata.with_source_provenance(
                metadata.source_provenance.with_derived_source_image_names((name,))
            ).payload_with(payload.data, payload.mask)

        return owned_runtime_value(value).map_slices(named_payload)

    @classmethod
    def compose_runtime_values(
        cls,
        values: Sequence[RuntimeValue],
        producer_group_scope: ComponentGroupScope | None = None,
    ) -> object:
        """Stack grouped image records while preserving payload context."""

        if producer_group_scope is None and len(values) == 1:
            return values[0].data

        from openhcs.core.aligned_image_payload import stack_image_payloads

        components = {value.key.scope.component for value in values}
        if None in components or len(components) != 1:
            raise ValueError(
                "Grouped image composition requires one exact declared component "
                f"axis, got {components!r}."
            )
        payloads = tuple(value.data for value in values)
        metadata_mode = RuntimeSlicePlaneAxis
        if producer_group_scope is None:
            return stack_image_payloads(payloads, metadata_mode=metadata_mode)
        return stack_image_payloads(
            payloads,
            memory_type=detect_memory_type(payloads[0].data),
            device_id=0,
            metadata_mode=metadata_mode,
        )

    @classmethod
    def normalize_group_scoped_payload(
        cls,
        output_plan: ArtifactOutputPlan,
        value: object,
    ) -> object:
        """Consume the singleton image axis represented by the artifact key."""

        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        projection = RuntimeSliceProjection.preserved_context_for_value(value)
        if projection is None:
            return value
        if projection.axis_size != 1:
            raise ValueError(
                f"Group-scoped scalar artifact {output_plan.name!r} for "
                f"{output_plan.group_component.name!r} cannot retain a declared "
                f"runtime-slice axis of size {projection.axis_size}."
            )
        return RuntimeSliceProjection.value_for_slice(
            value,
            projection.selected_plane(0),
        )

    @classmethod
    def reduce_materialization_records(
        cls,
        *,
        records: tuple[StoredRuntimeValue, ...],
        output_plan: ArtifactOutputPlan,
    ) -> tuple[StoredRuntimeValue, ...]:
        from openhcs.core.source_projection import OpenHCSPlaneAddress

        if not output_plan.materialization_uses_source_identity_filename():
            return records

        addressed_records: list[
            tuple[StoredRuntimeValue, OpenHCSPlaneAddress | None]
        ] = []
        records_by_address: dict[
            OpenHCSPlaneAddress,
            list[StoredRuntimeValue],
        ] = {}
        for record in records:
            metadata = record.materialization_payload().metadata
            address = OpenHCSPlaneAddress.from_complete_source_metadata(
                metadata.source_component_metadata
            )
            addressed_records.append((record, address))
            if address is not None:
                records_by_address.setdefault(address, []).append(record)

        reduced_records: list[StoredRuntimeValue] = []
        emitted_addresses: set[OpenHCSPlaneAddress] = set()
        for record, address in addressed_records:
            if address is None:
                reduced_records.append(record)
                continue
            if address in emitted_addresses:
                continue
            emitted_addresses.add(address)
            reduced_records.append(
                cls._materialization_record_for_scalar_address(
                    output_plan,
                    address,
                    tuple(records_by_address[address]),
                )
            )
        return tuple(reduced_records)

    @classmethod
    def _materialization_record_for_scalar_address(
        cls,
        output_plan: ArtifactOutputPlan,
        address: OpenHCSPlaneAddress,
        records: tuple[StoredRuntimeValue, ...],
    ) -> StoredRuntimeValue:
        if len(records) == 1:
            return records[0]

        owner_records = tuple(
            record
            for record in records
            if all(
                address.value_for(component) == value
                for component, value in record.key.scope.source_component_values
            )
        )
        if len(owner_records) != 1:
            raise ValueError(
                "Scalar image materialization requires one execution scope matching "
                f"source address {address!r} for artifact {output_plan.name!r}; "
                f"found {len(owner_records)} among "
                f"{tuple(record.key.scope for record in records)!r}."
            )

        scope_record = owner_records[0]
        scope_payload = scope_record.materialization_payload()
        for record in records:
            payload = record.materialization_payload()
            if not cls._materialization_payloads_are_equivalent(scope_payload, payload):
                raise ValueError(
                    "Conflicting scalar image materialization payloads for source "
                    f"address {address!r} and artifact {output_plan.name!r}: "
                    f"{scope_record.key.scope!r} != {record.key.scope!r}."
                )
        return scope_record

    @staticmethod
    def _materialization_payloads_are_equivalent(left: object, right: object) -> bool:
        import numpy as np

        if left.metadata != right.metadata:
            return False
        left_data = np.asarray(left.data)
        right_data = np.asarray(right.data)
        return left_data.dtype == right_data.dtype and np.array_equal(
            left_data, right_data, equal_nan=True
        )


class ObjectLabelsArtifactType(NominalPayloadKind, ImagePayloadArtifactKind):
    """Object-label array artifact type."""

    value = "object_labels"

    @classmethod
    def description(cls) -> str:
        return "object_labels payload"

    @classmethod
    def runtime_payload_type(cls) -> type:
        from openhcs.core.runtime_object_labels import ObjectLabelValue

        return ObjectLabelValue

    @classmethod
    def runtime_parameter_types(cls) -> tuple[type, ...]:
        return (cls.runtime_payload_type(),)

    @classmethod
    def contextualize_value(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        raise TypeError(
            f"Object-label output {type(output_value).__name__} has no "
            "registered nominal strategy; return an ObjectLabelValue or an "
            "image payload."
        )

    @classmethod
    def contextualize_image(
        cls,
        source_payload: object,
        output_value: ImagePayload,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        return output_value.object_label_output(source_payload, plane_projection)

    @classmethod
    def contextualize_aligned(
        cls,
        source_payload: object,
        output_value: RuntimeSliceAlignedValueSet,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        return output_value.object_label_output(source_payload, plane_projection)

    @classmethod
    def _bind_compiled_name(cls, name: str, value: object) -> object:
        """Bind or validate the compiled identity of one nominal label value."""

        from openhcs.core.runtime_object_labels import ObjectLabelSet

        if cls.accepts_runtime_payload(value):
            return ObjectLabelSet.named(name, value)
        return value

    @classmethod
    def normalize_runtime_payload(
        cls,
        name: str,
        value: object,
    ) -> object:
        """Bind scalar object labels to their compiled artifact identity."""

        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        return RuntimeSliceProjection.match_alignment(
            value,
            scalar=lambda scalar: cls._bind_compiled_name(name, scalar),
            aligned=lambda aligned: aligned,
        )

    @classmethod
    def normalize_source_payload(
        cls,
        data: object,
        channel_axis: int | None,
    ) -> tuple[object, int | None]:
        """Convert color-coded source labels into integer label IDs."""

        from openhcs.core.runtime_object_labels import normalize_source_label_data

        return normalize_source_label_data(data, channel_axis), None

    @classmethod
    def _aggregated(cls, name: str, labels: tuple[object, ...]) -> object:
        from openhcs.core.runtime_object_label_aggregation import (
            ObjectLabelPure2DSliceAggregator,
        )

        aggregated = ObjectLabelPure2DSliceAggregator.aggregate(
            labels,
            detect_memory_type(labels[0].labels),
            plane_axis=RuntimeSlicePlaneAxis,
        )
        return cls._bind_compiled_name(name, aggregated)

    @classmethod
    def compose_runtime_values(
        cls,
        values: Sequence[RuntimeValue],
        producer_group_scope: ComponentGroupScope | None = None,
    ) -> object:
        """Aggregate grouped object-label records into one runtime stack."""

        if producer_group_scope is None and len(values) == 1:
            return values[0].data
        labels = tuple(value.data for value in values)
        if len({value.representation for value in labels}) != 1:
            raise ValueError(
                "Cannot compose grouped object labels with mixed representations."
            )
        return cls._aggregated(values[0].name, labels)

    @classmethod
    def normalize_slice_aligned_value(
        cls,
        value: RuntimeSliceAlignedValueSet[object],
        output_plan: ArtifactOutputPlan,
        *,
        axis_id: str,
    ) -> object:
        """Aggregate object-label slices into one plane-scoped label domain."""

        slices = value.values
        if all(cls.accepts_runtime_payload(item) for item in slices):
            return cls._aggregated(output_plan.name, slices)
        return super().normalize_slice_aligned_value(
            value, output_plan, axis_id=axis_id
        )


class MeasurementBearingArtifactType(ArtifactType):
    """Artifact whose current payload exposes native measurement tables."""

    @classmethod
    @abstractmethod
    def measurement_tables(
        cls, value: RuntimeValue, dialect: MeasurementDialect
    ) -> tuple[MeasurementTable, ...]:
        """Derive table views without publishing a second artifact record."""


class MeasurementsArtifactType(NominalPayloadKind, MeasurementBearingArtifactType):
    """Measurement-table artifact type."""

    value = "measurements"
    payload_shape = TablePayloadShape

    @classmethod
    def runtime_payload_type(cls) -> type:
        from openhcs.core.runtime_measurements import MeasurementTable

        return MeasurementTable

    @classmethod
    def measurement_tables(
        cls, value: RuntimeValue, dialect: MeasurementDialect
    ) -> tuple[MeasurementTable, ...]:
        del dialect
        return (cast("MeasurementTable", value.data),)

    @staticmethod
    def _validate_table(
        output_value: MeasurementTable,
        target: OutputTarget,
        subject: MeasurementSubject,
    ) -> None:
        target.validate_payload_name(output_value)
        if output_value.subject != subject:
            raise ValueError(
                f"Measurement output {target.describe()} declares subject "
                f"{subject!r}, but returned {output_value.subject!r}."
            )

    @staticmethod
    def _contextualized_rows(
        rows: ColumnarRows,
        *,
        subject: MeasurementSubject,
        source_provenance: SourceImageProvenance,
    ) -> ColumnarRows:
        from openhcs.core.measurement_row_materialization import (
            MeasurementRowOwnership,
            measurement_rows_with_source_provenance,
        )

        owned_rows = MeasurementRowOwnership(
            object_name=subject.object_name,
            source_image_name=subject.source_image_name,
        ).annotate_rows(rows)
        if not TablePayloadShape.accepts(owned_rows):
            raise TypeError(
                "Measurement row ownership must preserve the nominal ColumnarRows "
                f"carrier, got {type(owned_rows).__name__}."
            )
        return measurement_rows_with_source_provenance(
            owned_rows,
            source_provenance,
        )

    @classmethod
    def contextualize_value(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        """Own returned rows as this output's table, in the source's context."""

        from openhcs.core.runtime_image_values import as_runtime_value
        from openhcs.core.runtime_measurements import MeasurementTable

        del plane_projection
        subject = target.require_measurement_subject()
        source_provenance = as_runtime_value(source_payload).image_metadata.source_provenance
        if cls.accepts_runtime_payload(output_value):
            cls._validate_table(output_value, target, subject)
            contextualized_provenance = (
                output_value.source_provenance.with_missing_from(source_provenance)
            )
            return output_value.replace_fields(
                rows=cls._contextualized_rows(
                    output_value.rows,
                    subject=subject,
                    source_provenance=contextualized_provenance,
                ),
                source_provenance=contextualized_provenance,
            )
        if not cls.payload_shape.accepts(output_value):
            raise TypeError(
                f"Measurement output {target.describe()} requires ColumnarRows "
                f"or MeasurementTable, got {type(output_value).__name__}."
            )
        return MeasurementTable(
            name=target.name,
            rows=cls._contextualized_rows(
                output_value,
                subject=subject,
                source_provenance=source_provenance,
            ),
            source_image_name=subject.source_image_name,
            subject=subject,
            source_provenance=source_provenance,
        )

    @classmethod
    def contextualize_output_from_projector(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projector: RuntimePlaneAxisProjector | None,
    ) -> object:
        """Validate nominal identity before generic plane projection inspects it."""

        subject = target.require_measurement_subject()
        if cls.accepts_runtime_payload(output_value):
            cls._validate_table(output_value, target, subject)
        return cls.contextualize_projected_output(
            source_payload,
            output_value,
            target,
            plane_projector,
        )

    @classmethod
    def validate_output_declaration(cls, spec: ArtifactSpec) -> None:
        """Reject incompatible row domains before payload-owner validation.

        The payload owner determines whether distinct named subjects can occupy
        the output. Native and ordinary recorded tables require one exact
        subject; row-owning recorders preserve each subject's identity.
        """

        subjects = spec.measurement_subjects()
        if len({(subject.scope, subject.id_field) for subject in subjects}) > 1:
            spec.measurement_subject()

    @classmethod
    def validate_native_output_declaration(cls, spec: ArtifactSpec) -> None:
        spec.require_measurement_subject()

    @classmethod
    def validate_recorded_output_declaration(
        cls,
        spec: ArtifactSpec,
        policy: type[AdapterRecordedArtifactOutputPolicy],
    ) -> None:
        policy.validate_measurement_subject(spec)

    @classmethod
    def runtime_parameter_types(cls) -> tuple[type, ...]:
        from openhcs.core.runtime_tabular_values import ColumnarRows

        return (ColumnarRows,)

    @classmethod
    def runtime_semantic_id(cls, data: object) -> str | None:
        if cls.accepts_runtime_payload(data):
            return data.runtime_semantic_id
        return None

    @classmethod
    def compose_runtime_values(
        cls,
        values: Sequence[RuntimeValue],
        producer_group_scope: ComponentGroupScope | None = None,
    ) -> object:
        """Concatenate exact producer-group measurement tables."""

        from openhcs.core.runtime_measurements import MeasurementTable

        del producer_group_scope
        return MeasurementTable.join(
            values[0].name, tuple(value.data for value in values)
        )

    @classmethod
    def materialization_payload(cls, value: RuntimeValue) -> object:
        if not cls.accepts_runtime_payload(value.data):
            cls.validate_runtime_payload(value.name, value.data)
        return value.data

    @classmethod
    def uses_aggregate_materialization_identity(cls, data: object) -> bool:
        """Name multi-plane measurement tables by artifact, not a sample plane."""

        if cls.accepts_runtime_payload(data):
            provenance = data.source_provenance
            return bool(
                provenance.varying_plane_component_values(AxisFamily.active().axes)
                or len(provenance.represented_source_identities) > 1
            )
        return False

    @classmethod
    def reduce_materialization_scope(
        cls,
        *,
        records: tuple[StoredRuntimeValue, ...],
        output_plan: ArtifactOutputPlan,
        group_key: str | None,
    ) -> tuple[StoredRuntimeValue, ...]:
        from openhcs.constants.constants import Backend
        from openhcs.core.runtime_artifact_values import RuntimeValue
        from openhcs.core.runtime_measurements import MeasurementTable
        from openhcs.core.runtime_stores import (
            RuntimeArtifactLocation,
            StoredRuntimeValue,
        )

        if len(records) <= 1:
            return records
        group_plan = output_plan.for_group(group_key)
        tables = tuple(cast(MeasurementTable, record.data) for record in records)
        table = MeasurementTable.join_artifact(output_plan.name, tables)
        value = RuntimeValue.normalize_for_execution_scope(
            group_plan,
            table,
            execution_scope=records[0].key.scope,
        )
        return (
            StoredRuntimeValue(
                key=value.key,
                data=value.data,
                materialization_source_metadata=value.materialization_source_metadata,
                location=RuntimeArtifactLocation(
                    path=group_plan.path,
                    backend=Backend.MEMORY.value,
                ),
            ),
        )


class ObjectLineageArtifactType(NominalPayloadKind, ArtifactType):
    """Internal directed object lineage used to project object measurements."""

    value = "object_lineage"
    payload_shape = TablePayloadShape

    @classmethod
    def runtime_payload_type(cls) -> type:
        from openhcs.core.runtime_relationships import ObjectRelationship

        return ObjectRelationship

    @classmethod
    def compose_runtime_values(
        cls,
        values: Sequence[RuntimeValue],
        producer_group_scope: ComponentGroupScope | None = None,
    ) -> object:
        """Reconstruct relationship records and retain grouped slice alignment."""

        relationships = tuple(value.data for value in values)
        if producer_group_scope is None and len(relationships) == 1:
            return relationships[0]
        return RuntimeSliceAlignedValues(relationships)


class RelationshipsArtifactType(ObjectLineageArtifactType):
    """Explicitly recorded directed relationship exported to external consumers."""

    value = "relationships"

    @classmethod
    def materialization_payload(cls, value: RuntimeValue) -> object:
        return value.data.as_table()


class TableArtifactType(ArtifactType):
    """Generic table artifact type."""

    value = "table"
    payload_shape = TablePayloadShape


class SpatialGridArtifactType(
    NominalPayloadKind, SourceContextKind, MeasurementBearingArtifactType
):
    """Spatial-grid mapping artifact type."""

    value = "spatial_grid"
    payload_shape = MappingPayloadShape

    @classmethod
    def description(cls) -> str:
        return "spatial grid mapping"

    @classmethod
    def runtime_payload_type(cls) -> type:
        from openhcs.core.runtime_spatial_grid import SpatialGrid

        return SpatialGrid

    @classmethod
    def runtime_parameter_types(cls) -> tuple[type, ...]:
        return (cls.runtime_payload_type(),)

    @classmethod
    def measurement_tables(
        cls, value: RuntimeValue, dialect: MeasurementDialect
    ) -> tuple[MeasurementTable, ...]:
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        return RuntimeSliceProjection.match_alignment(
            value.data,
            scalar=lambda grid: (grid.measurement_table(dialect),),
            aligned=lambda grids: grids.map_indexed_slices(
                lambda slice_index, grid: grid.measurement_table(
                    dialect, (slice_index,)
                )
            ).values,
        )

    @classmethod
    def contextualize_value(
        cls,
        source_payload: object,
        output_value: SpatialGrid,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        del target, plane_projection
        return output_value.replace_fields(
            source_provenance=output_value.source_provenance.with_missing_from(
                source_payload.metadata.source_provenance
            )
        )

    @classmethod
    def contextualize_aligned(
        cls,
        source_payload: object,
        output_value: RuntimeSliceAlignedValueSet,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        RuntimePlaneAxisValueProjection.require_axis_size(
            plane_projection,
            output_value.slice_count,
            value_name="Runtime-slice-aligned spatial grids",
        )
        return output_value.map_indexed_slices(
            lambda slice_index, grid: cls.contextualize_value(
                source_payload, grid, target, None
            ).replace_fields(slice_index=slice_index)
        )

    @classmethod
    def normalize_runtime_payload(
        cls,
        name: str,
        value: object,
    ) -> object:
        """Normalize scalar or runtime-slice grid returns to nominal values."""

        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
        from openhcs.core.runtime_spatial_grid import SpatialGrid

        def grid(item: object) -> SpatialGrid:
            return SpatialGrid.from_runtime_value(name, item)

        if isinstance(value, (list, tuple)):
            value = RuntimeSliceAlignedValues(tuple(value))
        return RuntimeSliceProjection.match_alignment(
            value,
            scalar=grid,
            aligned=lambda grids: grids.map_slices(grid),
        )

    @classmethod
    def compose_runtime_values(
        cls,
        values: Sequence[RuntimeValue],
        producer_group_scope: ComponentGroupScope | None = None,
    ) -> object:
        """Compose only spatial grids with identical declared slice domains."""

        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        del producer_group_scope
        grids = tuple(value.data for value in values)

        def layout(grid_value: object) -> tuple[object, ...]:
            return RuntimeSliceProjection.match_alignment(
                grid_value,
                scalar=lambda grid: ("scalar", grid.as_mapping()),
                aligned=lambda aligned: (
                    "runtime-slice-aligned",
                    tuple(grid.as_mapping() for grid in aligned.values),
                ),
            )

        first_layout = layout(grids[0])
        conflicting = tuple(
            index for index, grid in enumerate(grids) if layout(grid) != first_layout
        )
        if conflicting:
            raise ValueError(
                "Grouped spatial-grid composition requires identical grids and "
                f"identical runtime-slice alignment; values {conflicting!r} differ "
                "from the first."
            )
        return grids[0]

    @classmethod
    def materialization_payload(cls, value: RuntimeValue) -> object:
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
        from python_introspect import to_jsonable

        def mapping(grid: SpatialGrid) -> dict[str, object]:
            return {
                **grid.as_mapping(),
                "source_provenance": to_jsonable(grid.source_provenance),
            }

        return RuntimeSliceProjection.match_alignment(
            value.data,
            scalar=mapping,
            aligned=lambda grids: tuple(mapping(grid) for grid in grids.values),
        )


class SpatialGraphArtifactType(NominalPayloadKind, SourceContextKind, ArtifactType):
    """Spatial graph with edge paths, topology, and scalar edge features."""

    value = "spatial_graph"

    @classmethod
    def description(cls) -> str:
        return "spatial graph payload"

    @classmethod
    def runtime_payload_type(cls) -> type:
        from openhcs.core.runtime_spatial_graph import SpatialGraph

        return SpatialGraph

    @classmethod
    def runtime_parameter_types(cls) -> tuple[type, ...]:
        return (cls.runtime_payload_type(),)

    @classmethod
    def contextualize_value(
        cls,
        source_payload: object,
        output_value: object,
        target: OutputTarget,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> object:
        del plane_projection
        if not cls.accepts_runtime_payload(output_value):
            raise TypeError(
                "Spatial graph output requires SpatialGraph, got "
                f"{type(output_value).__name__}."
            )
        target.validate_payload_name(output_value)
        return output_value.contextualized_source_metadata(source_payload.metadata)


class MetadataArtifactType(ArtifactType):
    """Metadata mapping artifact type."""

    value = "metadata"
    payload_shape = MappingPayloadShape

    @classmethod
    def description(cls) -> str:
        return "metadata mapping"
