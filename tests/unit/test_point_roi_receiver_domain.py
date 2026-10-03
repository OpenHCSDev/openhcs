"""Receiver domain admission through existing main source declarations only.

No point producer/materialization, native endpoint, compiler or Root-only graph.
"""

import pytest
from polystore.roi import PointShape, ROI

from openhcs.core.roi_point_metadata import ROIFractionalZ
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import (
    OriginalSourceMetadata,
    SourceFilterPathMetadata,
    SourceVoxelSpacing,
)


def source_records(planes=4, origin=0):
    paths = tuple(f"/own-receiver/z{origin + index}.tif" for index in range(planes))
    records = tuple(
        dict(well="A01", site=1, channel=1, timepoint=1, z_index=origin + index)
        for index in range(planes)
    )
    for record, path in zip(records, paths, strict=True):
        OriginalSourceMetadata.from_mapping(
            {key: str(value) for key, value in record.items()}
        ).merge_into(record, path=path)
        SourceFilterPathMetadata.from_paths((path,)).merge_into(record, path=path)
        SourceVoxelSpacing((2.0, 0.65, 0.65)).merge_into(record, path=path)
    return paths, records


def admitted_domain(paths, records, coordinate=1.5):
    metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=paths, component_metadata=records
        )
    )
    rois = [ROIFractionalZ(coordinate).bind(ROI([PointShape(1.5, 2.5)]))]
    return ROIFractionalZ.source_component_domain(rois, metadata)


@pytest.mark.parametrize("planes,origin", ((1, 0), (4, 0), (4, 10)))
def test_receiver_keeps_full_original_records_and_order(planes, origin):
    paths, records = source_records(planes, origin)
    domain = admitted_domain(paths, records, 0 if planes == 1 else 1.5)
    assert tuple(dict(record) for record in domain) == records
    assert tuple(record["z_index"] for record in domain) == tuple(
        range(origin, origin + planes)
    )


@pytest.mark.parametrize(
    "field,value,error",
    (
        ("well", "B01", "vary outside Z"),
        ("site", 2, "vary outside Z"),
        ("channel", 2, "vary outside Z"),
        ("timepoint", 2, "vary outside Z"),
        ("well", None, "inconsistent components"),
        ("site", None, "inconsistent components"),
        ("channel", None, "inconsistent components"),
        ("timepoint", None, "inconsistent components"),
        ("z_index", 0, "consecutive and ordered"),
        ("z_index", 3, "consecutive and ordered"),
        ("z_index", None, "require z_index"),
        ("z_index", True, "must be integers"),
        ("z_index", 1.5, "must be integers"),
        ("z_index", "1.5", "must be integers"),
        ("OpenHCSSourceVoxelSpacingZYX", "2,0.7,0.7", "inconsistent calibration"),
        ("OpenHCSSourceVoxelSpacingUnit", "relative", "inconsistent calibration"),
    ),
)
def test_receiver_rejects_real_coordinate_or_calibration_difference(field, value, error):
    paths, records = source_records()
    if value is None:
        del records[1][field]
    else:
        records[1][field] = value
    with pytest.raises(ValueError, match=error):
        admitted_domain(paths, records)


@pytest.mark.parametrize("coordinate", (-0.5, 3.5))
def test_receiver_rejects_fractional_coordinate_outside_represented_planes(coordinate):
    with pytest.raises(ValueError, match="outside its source planes"):
        admitted_domain(*source_records(), coordinate=coordinate)
