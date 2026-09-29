"""Source-aligned evidence from one IdentifyPrimaryObjects execution.

These are review images, not new object sets. In particular the filtering
planes project the existing ObjectLabelPayload variants without changing their
identity domain or reconstructing rejected objects.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import NamedTuple, Tuple, get_type_hints

import numpy as np

from openhcs.core.artifacts import (
    ArtifactSidecarRole,
    ArtifactSidecarSourceRelation,
    ArtifactSpec,
    ArtifactViewerStreaming,
    ImageArtifactType,
    SourceStackLineageSourceRelation,
)
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    MaskedImagePayload,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_object_labels import ObjectLabelPayload, ObjectLabelVariant


@dataclass(frozen=True, slots=True)
class DiagnosticPlaneSource:
    """Decode source identity and validity once, sharing one mask across stages."""

    metadata: ImagePayloadMetadata
    validity_mask: np.ndarray

    @classmethod
    def from_image(cls, image: object) -> "DiagnosticPlaneSource":
        source_mask = image_payload_mask(image)
        return cls(
            image_payload_metadata(image),
            np.ones(np.asarray(image_payload_data(image)).shape, dtype=bool)
            if source_mask is None else np.asarray(source_mask, dtype=bool),
        )

    def plane(
        self, pixels: np.ndarray, *, validity_mask: np.ndarray | None = None
    ) -> MaskedImagePayload:
        """Attach source coordinates, but keep the stage's intensity semantics."""

        return MaskedImagePayload(
            data=pixels,
            mask=self.validity_mask if validity_mask is None else validity_mask,
            # Do not interpret a normalized response using its acquisition's
            # uint16 scale. Source address/coordinates remain untouched.
            metadata=self.metadata.replace_fields(
                intensity_scale=None,
                source_dtype=str(pixels.dtype),
                unit_interval_intensity=None,
                source_plane_intensity_scales=(),
                source_plane_dtypes=(),
            ),
        )


class DeclumpingEvidence(ABC):
    """Declumping owns whether its intermediate pixels were actually produced."""

    @abstractmethod
    def planes(
        self, source: DiagnosticPlaneSource
    ) -> tuple[MaskedImagePayload, MaskedImagePayload, MaskedImagePayload]:
        """Return response, maxima and labeled seeds in source coordinates."""


@dataclass(frozen=True, slots=True)
class ExecutedDeclumpingEvidence(DeclumpingEvidence):
    """The exact response and seeds used by this execution's watershed."""

    response: np.ndarray
    maxima: np.ndarray
    markers: np.ndarray

    def planes(
        self, source: DiagnosticPlaneSource
    ) -> tuple[MaskedImagePayload, MaskedImagePayload, MaskedImagePayload]:
        return (
            source.plane(self.response),
            source.plane(self.maxima),
            source.plane(self.markers),
        )


class UnexecutedDeclumpingEvidence(DeclumpingEvidence):
    """Disabled declumping or no foreground: no response/seed evidence exists.

    A wholly invalid plane means NOT EXECUTED, not a measured zero response.
    NaN response pixels make that distinction survive ordinary image export
    even where a reader does not expose the validity mask.
    """

    def planes(
        self, source: DiagnosticPlaneSource
    ) -> tuple[MaskedImagePayload, MaskedImagePayload, MaskedImagePayload]:
        shape = source.validity_mask.shape
        invalid = np.zeros(shape, dtype=bool)
        return (
            source.plane(np.full(shape, np.nan), validity_mask=invalid),
            source.plane(np.zeros(shape, dtype=bool), validity_mask=invalid),
            source.plane(np.zeros(shape, dtype=np.int32), validity_mask=invalid),
        )


class PrimaryObjectDiagnosticPlanes(NamedTuple):
    """Fixed, bounded stage planes, in acquisition pixel coordinates.

    Field declarations own artifact names, order and return-slot types.
    Threshold support is captured BEFORE hole filling. Initial components are
    captured AFTER pre-declump filling. Unedited and small-removed are the
    canonical payload variants after final identity remapping, not extra seeds.
    """

    threshold_support: MaskedImagePayload
    initial_components: MaskedImagePayload
    declump_response: MaskedImagePayload
    seed_maxima: MaskedImagePayload
    seed_markers: MaskedImagePayload
    unedited_objects: MaskedImagePayload
    small_removed_objects: MaskedImagePayload

    @classmethod
    def from_execution(
        cls,
        *,
        image: object,
        threshold_support: np.ndarray,
        initial_components: np.ndarray,
        declumping: DeclumpingEvidence,
        objects: ObjectLabelPayload,
    ) -> "PrimaryObjectDiagnosticPlanes":
        source = DiagnosticPlaneSource.from_image(image)
        response, maxima, markers = declumping.planes(source)
        return cls(
            source.plane(threshold_support),
            source.plane(initial_components),
            response,
            maxima,
            markers,
            source.plane(
                objects.variant_data.labels_for_variant(ObjectLabelVariant.UNEDITED),
            ),
            source.plane(
                objects.variant_data.labels_for_variant(ObjectLabelVariant.SMALL_REMOVED),
            ),
        )

    @classmethod
    def artifact_specs(
        cls, *, source_image: ArtifactSpec, objects: ArtifactSpec
    ) -> tuple[ArtifactSpec, ...]:
        """Project stage declarations into the ordinary image-sidecar contract."""

        prefix = ArtifactSidecarRole.QA_CHECKPOINT.name_for(objects.name)
        return tuple(
            ArtifactSpec.output(
                f"{prefix}__{stage}",
                ImageArtifactType,
                sidecar_role=ArtifactSidecarRole.QA_CHECKPOINT,
                viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
                relations=(
                    SourceStackLineageSourceRelation(source=source_image.ref()),
                    ArtifactSidecarSourceRelation(source=objects.ref()),
                ),
            )
            for stage in cls._fields
        )


# The callable ABI is a projection of the same typed plane declaration, not a
# second hand-written stage roster. The first three ordinary slots stay intact.
PrimaryObjectsRuntimeTuple = Tuple[
    (
        np.ndarray,
        DataclassMeasurementColumnarRows,
        ObjectLabelPayload,
        *get_type_hints(PrimaryObjectDiagnosticPlanes).values(),
    )
]
