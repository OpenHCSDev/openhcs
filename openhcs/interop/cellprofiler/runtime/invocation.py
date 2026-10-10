"""Typed CellProfiler invocation records and execution-mode utilities."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field, replace
from typing import ClassVar

import numpy as np

from openhcs.core.alias_property import AliasProperty
from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    ImageOutputBundle,
    ImagePayloadExecutionMode,
)
from openhcs.core.equivalence.keys import RuntimeMeasurementSourcePair
from openhcs.core.measurement_image_alignment import (
    MeasurementImageAlignmentSource,
    MeasurementImageReferenceDomain,
    PreparedMeasurementObjectLabels,
)
from openhcs.core.function_patterns import InvocationArtifactInputEdgePlan
from openhcs.core.runtime_adapters import (
    RuntimeAdapterRequest,
    RuntimeImageExecutionContext,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCompositionMode,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelMeasurementSource,
    ObjectLabelValue,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxisProjector,
)
from openhcs.core.runtime_slice_alignment import (
    RuntimeSliceAlignedValues,
    RuntimeSliceAlignedValueSet,
)
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.source_image_provenance import SourceImageProvenance
from openhcs.core.source_spatial_domain import CommonRuntimeValue
from openhcs.core.steps.function_runtime import RuntimeCallableArgument
from openhcs.core.runtime_array_values import array_geometry
from openhcs.core.axes import ColourAxis
from openhcs.core.runtime_image_values import image_metadata_of
from openhcs.core.runtime_image_values import owned_runtime_value


class CellProfilerSourceIdentityMixin:
    """Shared source-image identity behavior for CellProfiler runtime records."""

    SOURCE_ALIASES_FIELD_NAME: ClassVar[str]

    source_image_name: str | None
    source_aliases: tuple[str, ...]
    payload: RuntimeCallableArgument

    @property
    def has_source_identity(self) -> bool:
        """Return whether this record names a CellProfiler source-image surface."""
        return self.source_image_name is not None or bool(self.source_aliases)

    def source_image_pairs(self) -> tuple["CellProfilerSourceImagePair", ...]:
        """Return ordered pairwise source invocations for composed image payloads."""
        return tuple(
            CellProfilerSourceImagePair.from_parts(
                first_index=first_index,
                second_index=second_index,
                first_name=first_name,
                second_name=second_name,
            )
            for first_index, first_name in enumerate(self.source_aliases)
            for second_index, second_name in enumerate(self.source_aliases)
            if first_index < second_index
        )

    @property
    def source_surface_count(self) -> int:
        """Return how many CellProfiler source-image surfaces this record names."""
        if len(self.source_aliases) > 1:
            return len(self.source_aliases)
        if self.source_image_name is not None or self.source_aliases:
            return 1
        return 0

    def validate_source_identity(self) -> None:
        """Validate source alias declarations without module-level helper escape."""
        if not isinstance(self.source_aliases, tuple):
            raise TypeError(
                f"{self.SOURCE_ALIASES_FIELD_NAME} must be a tuple, "
                f"got {type(self.source_aliases).__name__}."
            )
        invalid = tuple(
            type(alias).__name__
            for alias in self.source_aliases
            if not isinstance(alias, str)
        )
        if invalid:
            raise TypeError(
                f"{self.SOURCE_ALIASES_FIELD_NAME} must contain str values, "
                f"got {invalid!r}."
            )

    def consumed_input_value(
        self,
        edge: InvocationArtifactInputEdgePlan,
        request: RuntimeAdapterRequest,
    ) -> RuntimeCallableArgument | None:
        """Return an actual callable input when this record owns its binding."""

        return None

    @classmethod
    def shared_source_image_name(
        cls,
        sources: tuple["CellProfilerSourceIdentityMixin", ...],
    ) -> str | None:
        """Return table-level source identity only when all sources share one."""
        return CommonRuntimeValue.from_values(
            source.source_image_name for source in sources
        ).single

    @classmethod
    def shared_source_payload(
        cls,
        sources: tuple["CellProfilerSourceIdentityMixin", ...],
    ) -> RuntimeCallableArgument | None:
        """Return a table-level source payload only for one shared provenance."""
        if not sources:
            return None
        provenances = tuple(
            source.payload.metadata.source_provenance.equality_identity
            for source in sources
        )
        if CommonRuntimeValue.from_values(provenances).single is None:
            return None
        return sources[0].payload

    @classmethod
    def composed_source_metadata(
        cls,
        sources: tuple["CellProfilerSourceIdentityMixin", ...],
        *,
        mode: ImagePayloadMetadataCompositionMode | None = None,
    ) -> ImagePayloadMetadata | None:
        """Return source metadata composed in runtime source order."""
        if not sources:
            return None
        if mode is None:
            mode = cls.source_metadata_composition_mode(sources)
        scalar_sources = tuple(
            provenance
            for source in sources
            for provenance in cls.source_provenances(source.payload)
        )
        if not scalar_sources:
            raise ValueError("Image metadata composition payloads cannot be empty.")
        provenances = tuple(
            (
                provenance.for_source_plane(0)
                if provenance.source_plane_count == 1
                else provenance
            )
            for provenance in scalar_sources
        )
        if not any(provenance.has_values for provenance in provenances):
            return ImagePayloadMetadata(plane_axis=mode.plane_axis)
        provenance = (
            SourceImageProvenance.stack(provenances, scalar_sources=scalar_sources)
            if mode is ImagePayloadMetadataCompositionMode.STACK
            else SourceImageProvenance.bundle(
                provenances, scalar_sources=scalar_sources
            )
        )
        return cls.metadata_for_source_provenance(provenance, mode=mode)

    @staticmethod
    def metadata_for_source_provenance(
        provenance: SourceImageProvenance,
        *,
        mode: ImagePayloadMetadataCompositionMode,
    ) -> ImagePayloadMetadata:
        """Carry a composed source axis without projecting its image pixels."""
        return ImagePayloadMetadata(
            source_provenance=provenance,
            plane_axis=mode.plane_axis,
        )

    @classmethod
    def aligned_source_metadata(
        cls,
        sources: tuple["CellProfilerSourceIdentityMixin", ...],
    ) -> ImagePayloadMetadata:
        """Compose measured images as contributors on their shared slice axis.

        Source aliases distinguish images, not runtime slices. Each image's
        nominal source roster supplies one entry per local slice; composition
        retains all images at that slice instead of appending image axes.
        """
        if not sources:
            raise ValueError("Aligned measurement metadata requires source images.")
        source_axes = tuple(cls.source_provenances(source.payload) for source in sources)
        planes = tuple(
            SourceImageProvenance.bundle(
                tuple(source.with_runtime_planes_as_contributors() for source in plane)
            ).with_runtime_planes_as_contributors()
            for plane in zip(*source_axes, strict=True)
        )
        if not planes:
            raise ValueError("Aligned measurement source axes cannot be empty.")
        provenance = (
            SourceImageProvenance.stack(planes)
            if any(plane.has_values for plane in planes)
            else SourceImageProvenance()
        )
        return cls.metadata_for_source_provenance(
            provenance,
            mode=ImagePayloadMetadataCompositionMode.STACK,
        )

    @classmethod
    def source_provenances(
        cls, payload: RuntimeCallableArgument
    ) -> tuple[SourceImageProvenance, ...]:
        """Read the declared runtime source roster without projecting image pixels."""
        if isinstance(payload, AlignedImageStack):
            return tuple(
                cls.scalar_source_provenance(value) for value in payload.slices
            )
        if isinstance(payload, RuntimeSliceAlignedValueSet):
            return tuple(cls.scalar_source_provenance(value) for value in payload.values)
        count = RuntimeSliceProjection.slice_count_from_values((payload,))
        metadata = image_metadata_of(payload)
        provenance = metadata.source_provenance
        if count is None:
            return (provenance,)
        if metadata.axis_position(ColourAxis) == 0:
            raise ValueError(
                "Image metadata cannot declare the same leading axis as both "
                "plane and channel."
            )
        return tuple(provenance.for_source_plane(index) for index in range(count))

    @staticmethod
    def scalar_source_provenance(
        payload: RuntimeCallableArgument,
    ) -> SourceImageProvenance:
        """Collapse an inner image bundle's source topology at its actual read epoch."""
        if not isinstance(payload, AlignedImageStack):
            return payload.metadata.source_provenance
        metadata = tuple(value.metadata for value in payload.slices)
        provenances = tuple(
            (
                fields.source_provenance.for_source_plane(0)
                if fields.plane_axis is None
                and fields.source_provenance.source_plane_count == 1
                else fields.source_provenance
            )
            for fields in metadata
        )
        preserve_topology = (
            len(metadata) == 1
            and metadata[0].plane_axis
            is ImagePayloadMetadataCompositionMode.BUNDLE.plane_axis
        )
        scalar_sources = tuple(fields.source_provenance for fields in metadata)
        provenance = SourceImageProvenance.bundle(
            provenances,
            scalar_sources=scalar_sources,
            preserve_single_topology=preserve_topology,
        )
        return (
            provenance.with_runtime_planes_as_contributors().with_common_scalar_identity_from_planes()
        )

    @classmethod
    def source_metadata_composition_mode(
        cls,
        sources: tuple["CellProfilerSourceIdentityMixin", ...],
    ) -> ImagePayloadMetadataCompositionMode:
        """Return the source-axis topology owned by this source class."""
        del sources
        return ImagePayloadMetadataCompositionMode.STACK


@dataclass(frozen=True, slots=True, kw_only=True)
class CellProfilerImageRequest(
    CellProfilerSourceIdentityMixin,
    RuntimeImageExecutionContext,
):
    """CellProfiler image domain, callable kwargs, and ordered source aliases."""

    SOURCE_ALIASES_FIELD_NAME: ClassVar[str] = "CellProfilerImageRequest.source_aliases"

    image_count: int
    payload: RuntimeCallableArgument
    source_aliases: tuple[str, ...] = ()
    kwargs: Mapping[str, object] = field(default_factory=dict)

    input_binding_request: RuntimeAdapterRequest | None = None
    input_edges: tuple[InvocationArtifactInputEdgePlan, ...] = ()
    primary_input_edges: tuple[InvocationArtifactInputEdgePlan, ...] = ()
    primary_input_payloads: tuple[RuntimeCallableArgument, ...] = ()

    def __post_init__(self) -> None:
        self.validate_source_identity()
        if self.primary_input_payloads and (
            len(self.primary_input_payloads) != len(self.primary_input_edges)
        ):
            raise ValueError("Primary input contexts must preserve exact binding order.")

    def consumed_input_value(
        self,
        edge: InvocationArtifactInputEdgePlan,
        request: RuntimeAdapterRequest,
    ) -> RuntimeCallableArgument | None:
        """Project the exact carrier consumed through an unchanged input origin."""

        binding_request = self.input_binding_request
        if (
            binding_request is None
            or request.source_binding_plan is not binding_request.source_binding_plan
            or not any(bound is edge for bound in self.input_edges)
        ):
            return None
        parameter_name = edge.spec.parameter_name
        if parameter_name is not None:
            if parameter_name not in self.kwargs:
                return None
            parameter_edges = tuple(
                bound
                for bound in self.input_edges
                if bound.spec.parameter_name == parameter_name
            )
            value = self.kwargs[parameter_name]
            if isinstance(value, tuple):
                values = value
            elif len(parameter_edges) > 1 and isinstance(value, AlignedImageStack):
                values = value.slices
            elif len(parameter_edges) == 1:
                return value
            else:
                return None
            if len(values) != len(parameter_edges):
                return None
            input_index = next(
                index for index, bound in enumerate(parameter_edges) if bound is edge
            )
            return values[input_index]
        for index, bound in enumerate(self.primary_input_edges):
            if bound is not edge:
                continue
            if self.primary_input_payloads:
                return self.primary_input_payloads[index]
            if isinstance(self.payload, ImageOutputBundle):
                return self.payload.output_payload(edge.spec.ref())
            if len(self.primary_input_edges) == 1:
                return self.payload
        return None


@dataclass(frozen=True, slots=True)
class CellProfilerSourceImageEndpoint:
    """One source image endpoint inside an ordered CellProfiler source pair."""

    index: int
    display_name: str

    name = AliasProperty("display_name")


@dataclass(frozen=True, slots=True)
class CellProfilerSourceImagePair:
    """Ordered pair of source-image endpoints inside a composed CP payload."""

    first: CellProfilerSourceImageEndpoint
    second: CellProfilerSourceImageEndpoint
    runtime_pair: RuntimeMeasurementSourcePair

    @classmethod
    def from_source_identity(
        cls,
        source_image_name: str | None,
        source_aliases: tuple[str, ...],
    ) -> "CellProfilerSourceImagePair | None":
        """Return the primary source pair implied by source identity fields."""
        del source_image_name
        match source_aliases:
            case (first_name, second_name):
                return cls.from_parts(
                    first_index=0,
                    second_index=1,
                    first_name=first_name,
                    second_name=second_name,
                )
            case _:
                return None

    @classmethod
    def from_parts(
        cls,
        *,
        first_index: int,
        second_index: int,
        first_name: str,
        second_name: str,
    ) -> "CellProfilerSourceImagePair":
        """Build a source pair from endpoint indexes and display names."""
        return cls(
            first=CellProfilerSourceImageEndpoint(first_index, first_name),
            second=CellProfilerSourceImageEndpoint(second_index, second_name),
            runtime_pair=RuntimeMeasurementSourcePair(first_name, second_name),
        )

    @property
    def source_image_name(self) -> str:
        """Return CellProfiler's table-level source identity for this pair."""
        return RuntimeMeasurementSourcePair.source_pair_name(
            self.first.display_name,
            self.second.display_name,
        )

    def invocation_kwargs(
        self,
        *,
        first_channel_kwarg: str,
        second_channel_kwarg: str,
    ) -> dict[str, int]:
        """Lower this source-pair invocation to CellProfiler channel kwargs."""
        return {
            first_channel_kwarg: self.first.index,
            second_channel_kwarg: self.second.index,
        }


CellProfilerMeasurementImageDomain = MeasurementImageReferenceDomain


@dataclass(frozen=True, slots=True, kw_only=True)
class CellProfilerMeasurementImage(
    CellProfilerSourceIdentityMixin,
    RuntimeImageExecutionContext,
    MeasurementImageAlignmentSource,
):
    """One resolved image payload used by object measurement modules."""

    registry_key: ClassVar[str] = "cellprofiler_measurement_image"
    SOURCE_ALIASES_FIELD_NAME: ClassVar[str] = (
        "CellProfilerMeasurementImage.source_aliases"
    )

    payload: RuntimeCallableArgument
    source_aliases: tuple[str, ...] = ()
    align_to_labels: bool = True
    reference_domain: CellProfilerMeasurementImageDomain = (
        CellProfilerMeasurementImageDomain.SOURCE_IMAGE
    )

    def __post_init__(self) -> None:
        object.__setattr__(self, "payload", owned_runtime_value(self.payload))
        self.validate_source_identity()
        if not isinstance(self.reference_domain, CellProfilerMeasurementImageDomain):
            raise TypeError(
                "CellProfilerMeasurementImage.reference_domain must be "
                "CellProfilerMeasurementImageDomain, got "
                f"{type(self.reference_domain).__name__}."
            )
        if (
            self.execution_mode
            is not ImagePayloadExecutionMode.ALIGNED_MULTI_IMAGE_STACK
        ):
            object.__setattr__(
                self, "payload", RuntimeSliceProjection.full_stack_value(self.payload)
            )

    @classmethod
    def source_metadata_composition_mode(
        cls,
        sources: tuple["CellProfilerMeasurementImage", ...],
    ) -> ImagePayloadMetadataCompositionMode:
        """Return source metadata topology declared by measurement reference domains."""
        if all(
            source.reference_domain is CellProfilerMeasurementImageDomain.OBJECT_LABELS
            for source in sources
        ):
            return ImagePayloadMetadataCompositionMode.BUNDLE
        return ImagePayloadMetadataCompositionMode.STACK

    @property
    def alignment_image(self) -> RuntimeCallableArgument:
        """Return this measurement image payload for alignment."""
        return self.payload

    @property
    def alignment_reference_domain(self) -> CellProfilerMeasurementImageDomain:
        """Return the reference domain that owns alignment shape decisions."""
        return self.reference_domain

    @property
    def alignment_source_aliases(self) -> tuple[str, ...]:
        """Return source aliases for source-binding projection."""
        return self.source_aliases

    @property
    def alignment_image_name(self) -> str:
        """Return a stable name for measurement-image alignment diagnostics."""
        source_image_name = self.source_image_name
        if source_image_name is not None:
            return source_image_name
        return "measurement image"

    def with_alignment_image(
        self,
        image: RuntimeCallableArgument,
    ) -> "CellProfilerMeasurementImage":
        """Return this source with image data and plane proof projected together."""

        plane_projection = self.plane_projection
        if plane_projection is not None:
            if isinstance(image, AlignedImageStack):
                aligned_projection = RuntimeSliceProjection.preserved_context_for_value(
                    image
                )
                if (
                    aligned_projection is None
                    or aligned_projection.axis is not plane_projection.axis
                    or aligned_projection.plane_index != plane_projection.plane_index
                    or aligned_projection.axis_size != plane_projection.axis_size
                ):
                    raise ValueError(
                        "Aligned measurement image runtime plane projection changed "
                        f"during alignment: {aligned_projection!r} != "
                        f"{plane_projection!r}."
                    )
            else:
                image_plane_axis = image.metadata.plane_axis
                if image_plane_axis is None:
                    plane_projection = None
                elif image_plane_axis is not plane_projection.axis:
                    raise ValueError(
                        "Aligned measurement image plane axis conflicts with its "
                        f"execution projection: {image_plane_axis.value!r} != "
                        f"{plane_projection.axis.value!r}."
                    )
                else:
                    plane_projection.validate_shape(
                        array_geometry(image).shape,
                        value_name="Aligned measurement image",
                    )
        return replace(
            self,
            payload=image,
            plane_projection=plane_projection,
        )

    def prepare_object_labels(
        self,
        label_payload: ObjectLabelValue,
        *,
        plane_projector: RuntimePlaneAxisProjector | None = None,
    ) -> PreparedMeasurementObjectLabels:
        """Prepare object labels according to this measurement image contract."""
        return PreparedMeasurementObjectLabels.from_request(
            self.object_label_alignment_request(
                label_payload,
                plane_projector=plane_projector,
                align_image_to_labels=self.align_to_labels,
            ),
        )

    def align_image_to_labels(
        self,
        label_payload: ObjectLabelValue,
        labels: ObjectLabelMeasurementSource,
        *,
        plane_projector: RuntimePlaneAxisProjector | None = None,
    ) -> RuntimeCallableArgument:
        """Project this measurement image payload into the supplied label domain."""
        return (
            self.alignment_request(
                labels=labels,
                label_payload=label_payload,
                plane_projector=plane_projector,
            )
            .aligned()
            .image
        )


@dataclass(frozen=True, slots=True)
class CellProfilerSliceAlignedValues(RuntimeSliceAlignedValues[np.ndarray]):
    """Non-image vector payload with one value array per object-label slice."""

    def __post_init__(self) -> None:
        if not self.slices:
            raise ValueError("CellProfilerSliceAlignedValues.slices cannot be empty.")
        if not isinstance(self.slices, tuple):
            raise TypeError(
                "CellProfilerSliceAlignedValues.slices must be a tuple, got "
                f"{type(self.slices).__name__}."
            )
        invalid = tuple(
            type(value).__name__
            for value in self.slices
            if not isinstance(value, np.ndarray)
        )
        if invalid:
            raise TypeError(
                "CellProfilerSliceAlignedValues.slices must contain ndarray values, "
                f"got {invalid!r}."
            )
