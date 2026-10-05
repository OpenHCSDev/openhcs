"""Tiny engineering declaration derived from the original494 volume fixture."""

from dataclasses import dataclass

import numpy as np

from openhcs.core.memory import numpy as numpy_func
from openhcs.core.artifacts import (
    ImageArtifactType, MainFlowStackOutputSpec, MeasurementsArtifactType,
    ObjectLabelsArtifactType, ObjectMeasurementSubjectRelation,
)
from openhcs.core.measurement_row_materialization import DataclassMeasurementColumnarRows
from openhcs.core.pipeline.function_contracts import artifact_outputs
from openhcs.core.runtime_measurements import (
    ObjectCoreMeasurementFeature, RuntimeMeasurementFeatureOwner,
)
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.materialization import (
    CsvOptions, MaterializationSpec, PointROIOptions, ROIOptions,
)


class FixtureCentreFeatureOwner(RuntimeMeasurementFeatureOwner):
    @classmethod
    def owns_measurement_feature_name(cls, feature_name: str) -> bool:
        return any(feature.feature_name == feature_name for feature in ObjectCoreMeasurementFeature)

    @classmethod
    def owns_primary_measurement_feature_name(cls, feature_name: str) -> bool:
        return cls.owns_measurement_feature_name(feature_name)


@dataclass(frozen=True)
class FixtureCentreRow:
    object_label: int
    center_z: float
    center_y: float
    center_x: float


FIXTURE_IMAGE = MainFlowStackOutputSpec.output('fixture_image_522', ImageArtifactType)
FIXTURE_LABELS = MainFlowStackOutputSpec.output(
    'fixture_labels_522', ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions(min_area=0)),
)
FIXTURE_CENTRES = MainFlowStackOutputSpec.output(
    'fixture_centres_522', MeasurementsArtifactType,
    measurement_feature_owner=FixtureCentreFeatureOwner,
    relations=(ObjectMeasurementSubjectRelation(source=FIXTURE_LABELS.ref(), id_field='object_label'),),
    materialization=MaterializationSpec(
        CsvOptions(),
        PointROIOptions(
            z_feature=ObjectCoreMeasurementFeature.CENTER_Z,
            y_feature=ObjectCoreMeasurementFeature.CENTER_Y,
            x_feature=ObjectCoreMeasurementFeature.CENTER_X,
        ),
    ),
)


@numpy_func(contract=ProcessingContract.PURE_3D)
@artifact_outputs(FIXTURE_IMAGE, FIXTURE_LABELS, FIXTURE_CENTRES)
def point_shape_volume_fixture_522(
    image: np.ndarray,
) -> tuple[np.ndarray, np.ndarray, DataclassMeasurementColumnarRows]:
    """Original494 computation; add only the declared native ROI publication."""
    if image.shape != (4, 5, 7) or image.dtype != np.dtype('uint16'):
        raise ValueError('Expected four-plane 5x7 uint16 engineering fixture')
    foreground = image > 0
    if not np.any(foreground):
        raise ValueError('Own positive engineering fixture unexpectedly empty')
    z, y, x = np.argwhere(foreground).mean(axis=0)
    labels = np.where(foreground, 7, 0).astype(np.int32)
    rows = DataclassMeasurementColumnarRows(
        (FixtureCentreRow(7, float(z), float(y), float(x)),), row_type=FixtureCentreRow,
    )
    return image.copy(), labels, rows
