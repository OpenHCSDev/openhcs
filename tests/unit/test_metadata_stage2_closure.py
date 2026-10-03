"""Public metadata record contract and its real private alignment consumers."""

import gc
import weakref
from dataclasses import FrozenInstanceError, dataclass, fields

import numpy as np
import pytest

from openhcs.core.measurement_image_alignment import (
    MeasurementImageLabelAlignmentRequest,
)
from openhcs.core.runtime_image_values import (
    ImageMetadataCarrier,
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.source_plane_alignment import SourcePayloadPlaneIdentity
from openhcs.core.steps.function_io import _preloaded_image_payload
from openhcs.serialization.json import to_jsonable
from tests.unit.test_measurement_image_alignment import (
    _MeasurementImageSource,
    _PlaneProjector,
)


@dataclass
class CalibratedMetadata(ImagePayloadMetadata):
    calibration: float = 4.0


def test_identity_record_keeps_public_metadata_field_schema_type_and_mutation():
    original = CalibratedMetadata(
        source_path="/input/A01.tif", source_component_metadata={"well": "A01"}
    )
    payload = original.payload_with(np.ones((3, 4)))
    record = SourcePayloadPlaneIdentity.from_payload(
        payload, SourceImageSetIdentityPolicy()
    )
    assert isinstance(record, ImageMetadataCarrier)
    assert not hasattr(record, "__dict__")
    assert {member.name for member in fields(record)} == {"metadata", "policy"}
    assert fields(record)[0].type == "ImagePayloadMetadata"
    assert type(record.metadata) is CalibratedMetadata
    assert record.metadata is original
    assert record.metadata is record.metadata
    assert set(to_jsonable(record)) == {"metadata", "policy"}
    initial = record.identities()
    record.metadata.source_component_metadata = {"well": "A02"}
    assert record.identities() != initial
    assert dict(record.metadata.source_component_metadata) == {"well": "A02"}
    with pytest.raises(FrozenInstanceError):
        record.metadata = ImagePayloadMetadata()


def test_identity_record_retains_metadata_without_pixel_payload_lifetime():
    data = np.ones((3, 4))
    payload = ImagePayloadMetadata(source_path="/input/image.tif").payload_with(data)
    record = SourcePayloadPlaneIdentity.from_payload(
        payload, SourceImageSetIdentityPolicy()
    )
    pixels = weakref.ref(data)
    expected = record.identities()
    del payload, data
    gc.collect()
    assert pixels() is None
    assert record.identities() == expected


def test_preload_preserves_existing_metadata_owner_without_backend_reads():
    class NoReadsFileManager:
        def physical_source_path(self, *args, **kwargs):
            pytest.fail("Existing source facts must not trigger backend reads.")

    data = np.arange(12).reshape(3, 4)
    metadata = CalibratedMetadata(source_path="/input/existing.tif")
    source = metadata.payload_with(data)
    result = _preloaded_image_payload(
        source,
        source_path="/unused.tif",
        read_backend="disk",
        filemanager=NoReadsFileManager(),
    )
    assert image_payload_data(result) is data
    assert image_payload_metadata(result) is metadata
    assert type(image_payload_metadata(result)) is CalibratedMetadata


def test_measurement_source_projection_preserves_actual_pixels_and_alias_selection():
    data = np.arange(24, dtype=np.float32).reshape(2, 3, 4)
    source = ImagePayloadMetadata(
        source_path="/input/channels.tif",
        source_image_names=("DNA", "RNA"),
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
    ).payload_with(data)
    request = MeasurementImageLabelAlignmentRequest(
        source=_MeasurementImageSource(source, source_aliases=("DNA", "RNA")),
        labels=np.zeros((3, 4), dtype=np.int32),
        plane_projector=_PlaneProjector(source_index=1, source_count=2),
    )
    projected = request.with_source_projected_image()
    np.testing.assert_array_equal(image_payload_data(projected.image), data[1])
    assert np.shares_memory(image_payload_data(projected.image), data)
    assert image_payload_metadata(projected.image).source_image_names == ("RNA",)
    assert image_payload_metadata(source).source_image_names == ("DNA", "RNA")
