"""Exact embedded acquisition placement using the ordinary positions artifact."""

from __future__ import annotations

import numpy as np
from polystore.source_tile_geometry import SourceTileGeometry

from openhcs.constants.constants import AllComponents
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.runtime_adapters import RuntimeAdapterRequest, runtime_adapter
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.backends.pos_gen.tile_position_artifacts import (
    TILE_POSITIONS_OUTPUT,
)


def _source_metadata(request: RuntimeAdapterRequest) -> ImagePayloadMetadata:
    """Bind final ordered source-plane provenance before array conversion."""
    return image_payload_metadata(request.source_payload)


@artifact_outputs(TILE_POSITIONS_OUTPUT)
@runtime_adapter("source_metadata", _source_metadata)
@numpy(contract=ProcessingContract.PURE_3D)
def acquisition_tile_positions(
    image_stack: np.ndarray,
    *,
    source_metadata: ImagePayloadMetadata,
) -> tuple[np.ndarray, list[tuple[float, float]]]:
    """Place each source tile at its exact embedded acquisition XY pixel offset.

    Select SITE as the variable component and group by CHANNEL. This produces
    the existing ``positions`` artifact for assemble_stack_cpu / assemble_stack_cupy;
    no grid kwargs or plate-level position provider is involved. SourceBindings
    ingestion proves identical site layouts and canvas dimensions across channels.
    The unchanged ordered image stack and ordered positions preserve the site's
    source provenance even for shuffled source ordering or sparse acquisitions.

    Offsets retain signed fractional pixels. The assembler applies one global
    floor/ceil translation to the common acquisition-relative extent. This is
    acquisition-coordinate placement, NOT image-correlation registration. Missing
    tiles remain holes; unknown coordinates, duplicates, resized input tiles and
    mixtures of wells/channels/time/Z fail explicitly. Seam quality still requires
    native raw-signal inspection before scientific acceptance.
    """
    if image_stack.ndim != 3 or not image_stack.shape[0]:
        raise ValueError(
            "Acquisition positions require a nonempty (site, Y, X) tile stack."
        )
    records = source_metadata.source_plane_metadata_records()
    if len(records) != image_stack.shape[0]:
        raise ValueError(
            "Acquisition positions require exact ordered metadata for every source tile."
        )
    identities = tuple(
        tuple(
            source_component_metadata_value(
                record.source_component_metadata or {},
                component,
            )
            for component in AllComponents
            if component is not AllComponents.SITE
        )
        for record in records
    )
    if len(set(identities)) != 1 or any(value is None for value in identities[0]):
        raise ValueError(
            "Acquisition positions require one well/channel/Z/time tile stack."
        )
    geometries = tuple(
        SourceTileGeometry.from_source_metadata(record.source_component_metadata)
        for record in records
    )
    if any(geometry is None for geometry in geometries):
        raise ValueError(
            "Source tiles lack exact embedded acquisition geometry; no grid is inferred."
        )
    sites = tuple(
        source_component_metadata_value(
            record.source_component_metadata or {}, AllComponents.SITE
        )
        for record in records
    )
    if None in sites or len(sites) != len(set(sites)):
        raise ValueError(
            "Every acquisition tile must carry a distinct source site identity."
        )
    for geometry in geometries:
        if (geometry.height_pixels, geometry.width_pixels) != tuple(
            image_stack.shape[-2:]
        ):
            raise ValueError(
                "Incoming tile shape differs from its declared acquisition canvas geometry."
            )
    positions = [(geometry.x_pixels, geometry.y_pixels) for geometry in geometries]
    if len(positions) != len(set(positions)):
        raise ValueError("Distinct acquisition tiles cannot share one XY position.")
    return image_stack, positions
