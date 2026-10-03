"""Metadata-owner request laws, independent of public namespace allocation."""

from dataclasses import dataclass
from dataclasses import replace
import gc
import weakref
from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.artifacts import (
    ArtifactSpec,
    ImageArtifactType,
    MeasurementsArtifactType,
    ArtifactOutputPlan,
)
from openhcs.core.callable_contract import CallableContract, CallableMetadata
from openhcs.core.runtime_image_values import (
    ImageMetadataPayload,
    ImageMetadataProjection,
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata_projection,
)
from openhcs.core.source_metadata import SOURCE_VOXEL_SPACING_FIELD
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelVariantData,
)
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.steps.function_output_identity import FunctionOutputIdentityAuthority
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.interop.cellprofiler.runtime.artifact_binding import (
    ImageArtifactTypeStrategy,
    RuntimeArtifactInputRequest,
)
from openhcs.interop.cellprofiler.runtime.invocation import (
    CellProfilerImageRequest,
    CellProfilerSourceIdentityMixin,
)
from openhcs.interop.cellprofiler.runtime.output_record_request import (
    CellProfilerOutputRecordRequest,
)
from openhcs.interop.cellprofiler.runtime.main_flow import cellprofiler_main_flow_output
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.runtime.measurement_recording import (
    CellProfilerMeasurementTableModule,
)
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows


def _metadata(**changes):
    return ImagePayloadMetadata(
        source_path="/input/A01_s001_w1_z001_t001.tif",
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "1",
            "z_index": "1",
            "timepoint": "1",
            "extension": ".tif",
        },
        **changes,
    )


def _request(payload):
    return CellProfilerImageRequest(
        payload=payload,
        source_image_name="DNA",
        image_count=1,
        execution_mode=ImagePayloadExecutionMode.NATURAL,
    )


def test_label_projection_preserves_computed_public_namespace_and_freshness():
    labels = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=np.ones((3, 4), dtype=np.int32)),
        source_path="/input/labels.tif",
    )
    owner = labels.metadata_projection
    public = owner.materialize_metadata()
    assert type(public) is ImagePayloadMetadata
    assert public is owner.materialize_metadata()
    assert public is not labels.metadata
    public.source_path = "/input/consumer.tif"
    assert labels.source_path == "/input/labels.tif"
    assert owner.read_value("source_provenance").source_path == "/input/consumer.tif"
    labels.source_path = "/input/new-labels.tif"
    fresh = labels.metadata_projection
    assert fresh.read_value("source_provenance").source_path == "/input/new-labels.tif"
    assert owner.read_value("source_provenance").source_path == "/input/consumer.tif"


def test_label_projection_retains_no_pixels_or_label_receiver():
    pixels = np.ones((3, 4), dtype=np.int32)
    labels = ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=pixels),
        source_path="/input/labels.tif",
    )
    pixel_ref, label_ref = weakref.ref(pixels), weakref.ref(labels)
    owner = labels.metadata_projection
    del pixels, labels
    gc.collect()
    assert pixel_ref() is None and label_ref() is None
    assert owner.read_value("source_provenance").source_path == "/input/labels.tif"


def test_label_projection_preserves_actual_overridden_metadata_error():
    error = ValueError("actual computed metadata error")

    class RefusingLabels(ObjectLabelPayload):
        @property
        def metadata(self):
            raise error

    labels = RefusingLabels(
        variant_data=ObjectLabelVariantData(labels=np.zeros((2, 3), dtype=np.int32))
    )
    with pytest.raises(ValueError) as caught:
        image_payload_metadata_projection(labels)
    assert caught.value is error


def test_artifact_alias_projection_preserves_pixels_mask_and_independent_metadata(
    monkeypatch,
):
    pixels = np.arange(12, dtype=np.float32).reshape(3, 4)
    mask = np.ones_like(pixels, dtype=bool)
    owner = _metadata(source_image_names=("Original",)).capture()
    payload = owner.payload_with(pixels, mask)
    spec = ArtifactSpec.input("DNA", ImageArtifactType)

    def no_public_namespace(self):
        raise AssertionError("An internal input binding forced the public namespace.")

    monkeypatch.setattr(
        ImageMetadataProjection, "materialize_metadata", no_public_namespace
    )
    derived = ImageArtifactTypeStrategy().raw_runtime_input_value(
        RuntimeArtifactInputRequest(spec=spec, value=payload)
    )
    assert image_payload_data(derived) is pixels
    assert image_payload_mask(derived) is mask
    derived_owner = image_payload_metadata_projection(derived)
    assert derived_owner is not owner
    assert ImageArtifactTypeStrategy().source_image_name_from_value(derived) is None
    assert derived_owner.read_value(
        "source_provenance"
    ).represented_source_image_names == (
        owner.read_value("source_provenance")
        .with_derived_source_image_names(("DNA",))
        .represented_source_image_names
    )
    assert owner.read_value("source_provenance").source_image_names == ("Original",)


def test_shared_source_payload_query_preserves_original_value_identity(monkeypatch):
    owner = _metadata().capture()
    first = ImageMetadataPayload.from_projection(np.zeros((3, 4)), owner)
    second = ImageMetadataPayload.from_projection(np.ones((3, 4)), owner)

    def no_public_namespace(self):
        raise AssertionError("A source query forced the public namespace.")

    monkeypatch.setattr(
        ImageMetadataProjection, "materialize_metadata", no_public_namespace
    )
    assert (
        CellProfilerSourceIdentityMixin.shared_source_payload(
            (_request(first), _request(second))
        )
        is first
    )
    assert CellProfilerSourceIdentityMixin.shared_source_payload(()) is None


def test_opaque_main_flow_returns_exact_output_without_namespace(monkeypatch):
    payload = ImageMetadataPayload.from_projection(
        np.ones((3, 4)), _metadata().capture()
    )

    def no_public_namespace(self):
        raise AssertionError("An opaque main-flow read forced public metadata.")

    monkeypatch.setattr(
        ImageMetadataProjection, "materialize_metadata", no_public_namespace
    )
    assert cellprofiler_main_flow_output(payload, payload, None) is payload


def test_main_flow_preserves_output_axis_error_before_input_access(monkeypatch):
    output = ImageMetadataPayload.from_projection(
        np.ones((2, 3, 4)),
        _metadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).capture(),
    )
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2
    )

    def no_public_namespace(self):
        raise AssertionError("The malformed output forced public metadata.")

    monkeypatch.setattr(
        ImageMetadataProjection, "materialize_metadata", no_public_namespace
    )
    with pytest.raises(ValueError, match="output axis conflicts"):
        cellprofiler_main_flow_output(object(), output, projection)


@dataclass
class ComponentAliasMetadata(ImagePayloadMetadata):
    @property
    def source_component_metadata(self):
        value = super().source_component_metadata
        return {**(value or {}), SOURCE_VOXEL_SPACING_FIELD: "1.0,2.5,2.5"}


def test_artifact_binding_keeps_real_subtype_component_alias_calibration():
    metadata = ComponentAliasMetadata(source_path="/input/calibrated.tif")
    original_spacing = metadata.source_voxel_spacing
    payload = metadata.capture().payload_with(np.ones((3, 4), dtype=np.float32))
    request = RuntimeArtifactInputRequest(
        spec=ArtifactSpec.input("DNA", ImageArtifactType), value=payload
    )
    derived = ImageArtifactTypeStrategy().raw_runtime_input_value(request)
    owner = image_payload_metadata_projection(derived)
    public = owner.materialize_metadata()
    assert type(public) is ComponentAliasMetadata
    assert public.source_component_metadata[SOURCE_VOXEL_SPACING_FIELD] == "1.0,2.5,2.5"
    assert public.source_voxel_spacing == original_spacing
    assert public.source_voxel_spacing.has_values


class DifferentComponentAliasMetadata(ImagePayloadMetadata):
    @property
    def source_component_metadata(self):
        return {**(super().source_component_metadata or {}), "channel": "7"}


class DifferentPathAliasMetadata(ImagePayloadMetadata):
    @property
    def source_path(self):
        return "/input/A01_s001_w7_z001_t001.tif"


def test_identity_preserves_determining_component_alias_value():
    metadata = DifferentComponentAliasMetadata(
        source_path="/input/A01_s001_w1_z001_t001.tif",
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "channel": "1",
            "z_index": "1",
            "timepoint": "1",
        },
    )
    assert metadata.source_provenance.source_component_metadata["channel"] == "1"
    parser = SourceSchemaFilenameParser()
    expected = FunctionOutputIdentityAuthority.identity_from_metadata(parser, metadata)
    assert expected.component_values["channel"] == 7
    actual = FunctionOutputIdentityAuthority.identity_from_metadata(
        parser, metadata.capture()
    )
    assert actual == expected


def test_identity_preserves_determining_path_alias_value():
    metadata = DifferentPathAliasMetadata(
        source_path="/input/A01_s001_w1_z001_t001.tif",
        source_component_metadata={
            "well": "A01",
            "site": "1",
            "z_index": "1",
            "timepoint": "1",
        },
    )
    assert metadata.source_provenance.source_path == "/input/A01_s001_w1_z001_t001.tif"
    parser = SourceSchemaFilenameParser()
    expected = FunctionOutputIdentityAuthority.identity_from_metadata(parser, metadata)
    assert expected.component_values["channel"] == 7
    actual = FunctionOutputIdentityAuthority.identity_from_metadata(
        parser, metadata.capture()
    )
    assert actual == expected


def test_public_composed_source_metadata_keeps_actual_namespace_contract():
    payload = _metadata().capture().payload_with(np.ones((3, 4), dtype=np.float32))
    source = _request(payload)
    owner = CellProfilerSourceIdentityMixin.composed_source_metadata_projection(
        (source,)
    )
    public = CellProfilerSourceIdentityMixin.composed_source_metadata((source,))
    assert type(public) is ImagePayloadMetadata
    assert public == owner.materialize_metadata()
    assert CellProfilerSourceIdentityMixin.composed_source_metadata(()) is None


def _record_request():
    output = ArtifactSpec.output("Measurements", MeasurementsArtifactType)
    payload = _metadata().capture().payload_with(np.ones((3, 4), dtype=np.float32))
    return CellProfilerOutputRecordRequest(
        callable_contract=CallableContract(
            func=lambda image: image,
            function_name="metadata_override",
            module_name=__name__,
            metadata=CallableMetadata(artifact_outputs=(output,)),
        ),
        active_input_edges=(),
        adapter=SimpleNamespace(),
        spec=output,
        output_plan=ArtifactOutputPlan(
            name=output.name,
            path="/memory/measurements.pkl",
            artifact_type=output.artifact_type,
        ),
        output_value=MeasurementSparseColumnarRows.from_rows((), fields=()),
        source=_request(payload),
        call_kwargs={},
        current_image=payload,
    )


def test_measurement_table_preserves_external_public_override_dispatch():
    rows = MeasurementSparseColumnarRows.from_rows((), fields=())
    metadata = _metadata()

    class ExternalModule(CellProfilerModule):
        @classmethod
        def measurement_record_rows(cls, request):
            return rows

        @classmethod
        def measurement_record_object_name(cls, request, rows):
            return None

        @classmethod
        def measurement_record_source_image_name(cls, request, rows):
            return "DNA"

        @classmethod
        def measurement_record_source_metadata(cls, request, rows):
            metadata.source_path = "/input/external-override.tif"
            return metadata

        @classmethod
        def measurement_record_source_metadata_projection(cls, request, rows):
            raise AssertionError("Public module override was bypassed.")

    table = ExternalModule.measurement_table(_record_request())
    assert table.source_provenance.source_path == "/input/external-override.tif"


def test_measurement_table_preserves_external_public_error_identity():
    error = ValueError("external public metadata failure")
    rows = MeasurementSparseColumnarRows.from_rows((), fields=())

    class ExternalModule(CellProfilerModule):
        @classmethod
        def measurement_record_rows(cls, request):
            return rows

        @classmethod
        def measurement_record_object_name(cls, request, rows):
            return None

        @classmethod
        def measurement_record_source_image_name(cls, request, rows):
            return "DNA"

        @classmethod
        def measurement_record_source_metadata(cls, request, rows):
            raise error

    with pytest.raises(ValueError) as caught:
        ExternalModule.measurement_table(_record_request())
    assert caught.value is error


def test_measurement_source_preserves_external_public_composition_override():
    error = ValueError("external source composition error")

    class ExternalSource(CellProfilerImageRequest):
        @classmethod
        def composed_source_metadata(cls, sources, *, mode=None):
            raise error

        @classmethod
        def composed_source_metadata_projection(cls, sources, *, mode=None):
            raise AssertionError("Public source composition override was bypassed.")

    request = _record_request()
    request = replace(
        request,
        source=ExternalSource(
            payload=request.current_image,
            source_image_name="DNA",
            image_count=1,
            execution_mode=ImagePayloadExecutionMode.NATURAL,
        ),
    )
    with pytest.raises(ValueError) as caught:
        CellProfilerMeasurementTableModule.measurement_record_source_metadata(
            request,
            request.output_value,
        )
    assert caught.value is error
