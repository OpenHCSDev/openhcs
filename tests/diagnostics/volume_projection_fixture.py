"""Versioned scalar-volume probe using the existing projection declarations.

This is a synthetic publication fixture, not a microscopy analysis recipe.
Selection and full-stack inspection are separate ordinary FunctionSteps.
The PipelineDocument declares Z stacking; PURE_3D does not choose an axis.
"""

from dataclasses import dataclass

from arraybridge import ArrayPayload
import numpy as np

from openhcs.core.artifacts import (
    ImageArtifactType,
    MainFlowPlaneProjectionOutputSpec,
    MainFlowStackOutputSpec,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
)
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.projected_image_output import SelectedPlaneImageOutput
from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
from openhcs.core.runtime_measurements import RuntimeMeasurementFeature, RuntimeMeasurementFeatureOwner
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.materialization import CsvOptions, MaterializationSpec, ROIOptions


class VolumeProjectionFixtureFeature(RuntimeMeasurementFeature):
    PIXEL_COUNT = "pixel_count"


class VolumeProjectionFixtureFeatureOwner(RuntimeMeasurementFeatureOwner):
    @classmethod
    def owns_measurement_feature_name(cls, feature_name: str) -> bool:
        return any(feature.feature_name == feature_name for feature in VolumeProjectionFixtureFeature)

    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name: str) -> bool:
        return cls.owns_measurement_feature_name(feature_name)


@dataclass(frozen=True)
class VolumeProjectionFixtureRow:
    slice_index: int
    object_label: int
    pixel_count: int


SELECTED_VOLUME = MainFlowPlaneProjectionOutputSpec.output(
    "selected_volume_fixture_v2", ImageArtifactType,
)
VOLUME_IMAGE = MainFlowStackOutputSpec.output("volume_fixture_image_v2", ImageArtifactType)
VOLUME_LABELS = MainFlowStackOutputSpec.output(
    "volume_fixture_labels_v2", ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions(min_area=0)),
)
VOLUME_ROWS = MainFlowStackOutputSpec.output(
    "volume_fixture_rows_v2", MeasurementsArtifactType,
    measurement_feature_owner=VolumeProjectionFixtureFeatureOwner,
    relations=(ObjectMeasurementSubjectRelation(source=VOLUME_LABELS.ref(), id_field="object_label"),),
    materialization=MaterializationSpec(CsvOptions()),
)


@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(SELECTED_VOLUME)
def select_volume_fixture_planes_v2(
    image: ArrayPayload,
    plane_indices: tuple[int, ...] = (),
) -> SelectedPlaneImageOutput:
    """Select ordered planes through the existing source-projection owner."""
    pixels = image_payload_data(image)
    if pixels.ndim != 3:
        raise ValueError("Expected a scalar ZYX fixture")
    indices = plane_indices or tuple(range(pixels.shape[0]))
    return SelectedPlaneImageOutput(np.take(pixels, indices, axis=0), indices)


@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(VOLUME_IMAGE, VOLUME_LABELS, VOLUME_ROWS)
def inspect_volume_fixture_v2(
    image: ArrayPayload,
) -> tuple[ArrayPayload, ArrayPayload, DataclassMeasurementColumnarRows]:
    """Preserve the entire actual input stack when publishing labels and rows."""
    pixels = image_payload_data(image)
    if pixels.ndim != 3 or not np.issubdtype(pixels.dtype, np.integer):
        raise ValueError("Expected an integer scalar ZYX fixture")
    if np.any(pixels < 0):
        raise ValueError("Fixture object IDs must be non-negative")
    metadata = image_payload_metadata(image)
    labels = pixels.astype(np.int32, copy=True)
    rows = tuple(
        VolumeProjectionFixtureRow(index, int(label), int(np.count_nonzero(plane == label)))
        for index, plane in enumerate(labels)
        for label in np.unique(plane)
        if label != 0
    )
    return (
        metadata.payload_with(pixels.copy()),
        metadata.payload_with(labels),
        DataclassMeasurementColumnarRows(rows, row_type=VolumeProjectionFixtureRow),
    )
