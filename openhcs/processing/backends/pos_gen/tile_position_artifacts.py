"""Shared artifact declaration for ordered, host-valued tile positions.

Positions are signed floating-point (X, Y) pixel offsets in incoming tile order.
The JSON materialization preserves that runtime payload without scaling,
rounding, grid inference, or changing the positions consumed by assemblers.
"""

from openhcs.core.artifacts import ArtifactSpec, SpecialArtifactType
from openhcs.processing.materialization import (
    JsonOptions,
    MaterializationSpec,
    MaterializedFilenameIdentity,
)

TILE_POSITIONS_OUTPUT = ArtifactSpec.output(
    "positions",
    SpecialArtifactType,
    materialization=MaterializationSpec(
        JsonOptions(filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME)
    ),
)
