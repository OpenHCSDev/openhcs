"""Saved label admission retains declared runtime axes, never guessed Z axes."""

from __future__ import annotations

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.artifacts import ArtifactSpec, ObjectLabelsArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_object_label_domains import ObjectLabelDomainScope
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.interop.cellprofiler.runtime.artifact_binding import (
    RuntimeArtifactInputRequest, RuntimeArtifactTypeStrategy,
)
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.shape import MeasureObjectSizeShapeModule, measure_object_size_shape


def _source(labels, *, axis=RuntimePlaneAxis.RUNTIME_SLICE, plane_count=None, spacing=(1.3556, 1.3556)):
    count = labels.shape[0] if plane_count is None else plane_count
    return ImagePayloadMetadata(
        plane_axis=axis,
        source_image_names=("saved_labels",) * count,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/synthetic/A01_s001_w{index + 1}_labels.tif" for index in range(count)),
            component_metadata=tuple({"well": "A01", "site": "1", "channel": str(index + 1)} for index in range(count)),
        ),
        source_voxel_spacing=SourceVoxelSpacing(spacing),
    ).payload_with(labels, None)


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_original_artifact_admission_and_full_stack_shape_keep_2d_planes(axis):
    labels = np.zeros((2, 8, 9), dtype=np.int32)
    labels[0, 1:3, 2:5] = 29
    labels[1, 2:5, 3:7] = 106
    source = _source(labels, axis=axis)
    source_bytes = labels.tobytes()
    spec = ArtifactSpec.input("saved_labels", ObjectLabelsArtifactType, parameter_name="labels")
    value = RuntimeArtifactTypeStrategy.for_artifact_type(spec.artifact_type).runtime_input_value(
        RuntimeArtifactInputRequest(spec=spec, value=source)
    )
    assert value.domain.scope is ObjectLabelDomainScope.PLANE
    assert value.plane_axis is axis
    assert value.domain.declared_object_id_domains == ((29,), (106,))
    assert value.source_provenance.identity() == source.metadata.source_provenance.identity()
    planes = value.measurement_planes()
    assert tuple(plane.labels.shape for plane in planes) == ((8, 9), (8, 9))
    for index, plane in enumerate(planes):
        np.testing.assert_array_equal(plane.labels, labels[index])
        assert plane.parent_image_source_voxel_spacing == SourceVoxelSpacing((1.3556, 1.3556))

    contract = CallableContract.from_callable(measure_object_size_shape)
    _image, rows = CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), source,
        {"labels": value, "calculate_advanced": False, "calculate_zernikes": False},
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )
    area = MeasureObjectSizeShapeModule.MeasurementFeature.AREA.value
    # The original AreaShape owner declares ROW_SEQUENCE and a dense extent
    # through each plane's maximum ID, not two sparse-ID measurement rows.
    # Check the entire existing vector, including every missing-value slot.
    expected_area = np.full(29 + 106, np.nan)
    expected_area[0] = 6.0
    expected_area[29] = 12.0
    np.testing.assert_array_equal(tuple(row[area] for row in rows), expected_area)
    assert "AreaShape_Volume" not in tuple(field.name for field in rows.fields)
    assert labels.tobytes() == source_bytes


def test_singleton_runtime_slice_is_not_a_physical_volume():
    labels = np.zeros((1, 6, 7), dtype=np.int32)
    labels[0, 1:4, 2:5] = 61
    value = SourceImageObjectLabelBuildRequest(image=_source(labels), labels=labels).payload()
    assert value.domain.declared_object_id_domains == ((61,),)
    assert value.measurement_planes()[0].labels.shape == (6, 7)


def test_declared_runtime_planes_can_each_contain_a_genuine_calibrated_volume():
    labels = np.ones((2, 3, 6, 7), dtype=np.int32)
    value = SourceImageObjectLabelBuildRequest(
        image=_source(labels, spacing=(2.0, 1.3556, 1.3556)), labels=labels,
    ).payload()
    assert tuple(plane.labels.shape for plane in value.measurement_planes()) == ((3, 6, 7), (3, 6, 7))
    assert value.parent_image_source_voxel_spacing.spacing_for_ndim(3) == (2.0, 1.3556, 1.3556)


def test_undeclared_volume_and_explicit_payload_override_are_not_guessed_planar():
    labels = np.ones((2, 6, 7), dtype=np.int32)
    for source, options in (
        (_source(labels, axis=None, spacing=(2.0, 1.3556, 1.3556)), {}),
        (_source(labels), {"domain_scope": ObjectLabelDomainScope.PAYLOAD}),
    ):
        value = SourceImageObjectLabelBuildRequest(image=source, labels=labels, **options).payload()
        assert value.domain.scope is ObjectLabelDomainScope.PAYLOAD
        assert value.plane_axis is None
        assert value.measurement_planes()[0].labels.shape == (2, 6, 7)
    with pytest.raises(ValueError, match="Cannot project 2-D source voxel spacing onto 3-D data"):
        SourceVoxelSpacing((1.3556, 1.3556)).spacing_for_ndim(3)


@pytest.mark.parametrize("plane_count", (0, 1, 3))
def test_declared_axis_rejects_missing_or_conflicting_cardinality(plane_count):
    labels = np.ones((2, 6, 7), dtype=np.int32)
    with pytest.raises(ValueError):
        SourceImageObjectLabelBuildRequest(image=_source(labels, plane_count=plane_count), labels=labels).payload()


def test_declared_axis_rejects_payload_wide_ids_and_mismatched_label_geometry():
    labels = np.ones((2, 6, 7), dtype=np.int32)
    source = _source(labels)
    with pytest.raises(ValueError, match="per-plane domains"):
        SourceImageObjectLabelBuildRequest(image=source, labels=labels, declared_object_ids=(1,)).payload()
    with pytest.raises(ValueError, match="spatial shape"):
        SourceImageObjectLabelBuildRequest(image=source, labels=np.ones((2, 5, 7), dtype=np.int32)).payload()


def test_explicit_projection_conflicting_with_source_declaration_is_rejected():
    labels = np.ones((2, 6, 7), dtype=np.int32)
    with pytest.raises(ValueError, match="conflicts"):
        SourceImageObjectLabelBuildRequest(
            image=_source(labels), labels=labels,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2),
        ).payload()


class PhysicalCalibrationRequired:
    """Independent admission capability for a new physical-measurement leaf."""

    def payload(self, **kwargs):
        SourceVoxelSpacing.require_physical_pixel_size((self.metadata.source_voxel_spacing,))
        return super().payload(**kwargs)


class CalibratedSavedLabels(PhysicalCalibrationRequired, SourceImageObjectLabelBuildRequest):
    """A new declaration composes calibration admission with the existing builder."""


def test_new_calibrated_leaf_executes_cooperative_admission_and_plane_building():
    labels = np.ones((2, 6, 7), dtype=np.int32)
    value = CalibratedSavedLabels(image=_source(labels), labels=labels).payload()
    assert value.domain.scope is ObjectLabelDomainScope.PLANE
    assert len(value.measurement_planes()) == 2
    with pytest.raises(ValueError, match="Physical scalar pixel size requires"):
        CalibratedSavedLabels(image=_source(labels, spacing=()), labels=labels).payload()
    assert SourceImageObjectLabelBuildRequest(image=_source(labels, spacing=()), labels=labels).payload().domain.scope is ObjectLabelDomainScope.PLANE
