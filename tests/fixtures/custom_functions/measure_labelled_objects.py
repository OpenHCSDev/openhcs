"""Per-object measurements with scikit-image as an OpenHCS custom function.

Consumes the label stack that ``cellpose_segment`` (neighbouring file) publishes
as ``cellpose_labels`` and the image flowing through the pipeline. Declared with
the NumPy memory type: whatever library produced the image and the labels,
OpenHCS hands this function NumPy arrays.
"""

from dataclasses import dataclass

import numpy as np
from skimage.measure import regionprops

from openhcs.core.artifacts.kinds import MeasurementsArtifactType, ObjectLabelsArtifactType
from openhcs.core.artifacts.relations import ObjectMeasurementSubjectRelation
from openhcs.core.artifacts.specs import ArtifactSpec
from openhcs.core.materialization import CsvOptions, MaterializationSpec
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs


@dataclass(frozen=True)
class ObjectMeasurement:
    """Shape and intensity of one labelled object."""

    slice_index: int
    label: int
    area_px: float
    centroid_y: float
    centroid_x: float
    eccentricity: float
    mean_intensity: float


LABELS = ArtifactSpec.input("cellpose_labels", ObjectLabelsArtifactType, parameter_name="labels")


@numpy
@artifact_inputs(LABELS)
@artifact_outputs(
    ArtifactSpec(
        "object_measurements",
        MeasurementsArtifactType,
        materialization=MaterializationSpec(CsvOptions()),
        relations=(
            ObjectMeasurementSubjectRelation(source=LABELS.ref(), id_field="label"),
        ),
    ),
)
def measure_labelled_objects(
    image,
    labels,
    min_area_px: int = 0,
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows]:
    """Measure area, position, eccentricity and mean intensity of every object.

    Args:
        image: Image stack (planes, Y, X) the intensities are read from.
        labels: Label stack from ``cellpose_segment``, one plane per image plane.
        min_area_px: Objects smaller than this many pixels are left out.

    Returns:
        The unchanged image and one row per object.
    """
    rows = [
        ObjectMeasurement(
            slice_index=index,
            label=int(region.label),
            area_px=float(region.area),
            centroid_y=float(region.centroid[0]),
            centroid_x=float(region.centroid[1]),
            eccentricity=float(region.eccentricity),
            mean_intensity=float(region.intensity_mean),
        )
        for index, (plane, label_plane) in enumerate(zip(np.asarray(image), np.asarray(labels)))
        for region in regionprops(np.asarray(label_plane, dtype=np.int32), intensity_image=plane)
        if region.area >= min_area_px
    ]
    return image, DataclassMeasurementColumnarRows(rows, ObjectMeasurement)
