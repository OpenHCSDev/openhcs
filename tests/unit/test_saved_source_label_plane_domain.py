"""Saved label admission retains declared runtime axes, never guessed Z axes."""

from __future__ import annotations

import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactSpec, ObjectLabelsArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_measurements import MeasurementRowAxisField
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_object_label_domains import ObjectLabelDomainScope
from openhcs.core.runtime_tabular_values import MeasurementObjectRowIdentity
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.interop.cellprofiler.runtime.output_recording import (
    CellProfilerOutputRecorder,
)
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.shape import MeasureObjectSizeShapeModule, measure_object_size_shape
from openhcs.core.image_payload_execution_mode import (
    FullStackExecution,
)


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


def _saved_label_input(source):
    spec = ArtifactSpec.input("saved_labels", ObjectLabelsArtifactType, parameter_name="labels")
    return CellProfilerOutputRecorder.for_artifact_type(spec.artifact_type).runtime_input_value(
        spec=spec, value=source
    )


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
@pytest.mark.parametrize("plane_count", (1, 2))
def test_explicit_object_projection_preserves_axis_without_acquisition_provenance(
    axis, plane_count,
):
    labels = np.ones((plane_count, 6, 7), dtype=np.int32)
    source = ImagePayloadMetadata(plane_axis=axis).payload_with(labels)
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=axis, axis_size=plane_count,
    )
    payload = SourceImageObjectLabelBuildRequest(
        image=source, labels=labels, plane_projection=projection,
    ).payload()

    assert payload.plane_axis is axis
    assert payload.domain.declared_object_id_domains == ((1,),) * plane_count
    assert payload.source_provenance == source.metadata.source_provenance
    np.testing.assert_array_equal(payload.labels, labels)
    other_axis = next(member for member in RuntimePlaneAxis if member is not axis)
    with pytest.raises(ValueError, match="conflicts with the source-image axis"):
        SourceImageObjectLabelBuildRequest(
            image=source, labels=labels,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=other_axis, axis_size=plane_count,
            ),
        ).payload()


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_original_artifact_admission_and_full_stack_shape_keep_2d_planes(axis):
    labels = np.zeros((2, 8, 9), dtype=np.int32)
    labels[0, 1:3, 2:5] = 29
    labels[1, 2:5, 3:7] = 106
    source = _source(labels, axis=axis)
    source_bytes = labels.tobytes()
    spec = ArtifactSpec.input("saved_labels", ObjectLabelsArtifactType, parameter_name="labels")
    value = CellProfilerOutputRecorder.for_artifact_type(spec.artifact_type).runtime_input_value(
        spec=spec, value=source
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
        execution_mode=FullStackExecution,
    )
    area = MeasureObjectSizeShapeModule.MeasurementFeature.AREA.value
    # Raw shape rows retain the exact authored label domain of each plane.
    # Export completion separately projects that domain to CP row ordinals.
    assert rows.object_row_identity is MeasurementObjectRowIdentity.LABEL_ID
    assert tuple(
        (
            row[MeasurementRowAxisField.SLICE_INDEX.value],
            row[MeasurementRowAxisField.OBJECT_LABEL.value],
            row[area],
        )
        for row in rows
    ) == ((0, 29, 6.0), (1, 106, 12.0))
    assert "AreaShape_Volume" not in tuple(field.name for field in rows.fields)
    assert labels.tobytes() == source_bytes


def test_singleton_runtime_slice_is_not_a_physical_volume():
    labels = np.zeros((1, 6, 7), dtype=np.int32)
    labels[0, 1:4, 2:5] = 61
    value = _saved_label_input(_source(labels))
    assert value.domain.declared_object_id_domains == ((61,),)
    assert value.measurement_planes()[0].labels.shape == (6, 7)


def test_declared_runtime_planes_can_each_contain_a_genuine_calibrated_volume():
    labels = np.ones((2, 3, 6, 7), dtype=np.int32)
    value = _saved_label_input(_source(labels, spacing=(2.0, 1.3556, 1.3556)))
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
        _saved_label_input(_source(labels, plane_count=plane_count))


def test_declared_axis_rejects_payload_wide_ids_and_mismatched_label_geometry():
    labels = np.ones((2, 6, 7), dtype=np.int32)
    source = _source(labels)
    projection = RuntimePlaneAxisValueProjection.from_source_declaration(
        source.metadata.plane_axis, source.metadata.source_provenance,
    )
    with pytest.raises(ValueError, match="per-plane domains"):
        SourceImageObjectLabelBuildRequest(
            image=source, labels=labels, declared_object_ids=(1,),
            plane_projection=projection,
        ).payload()
    with pytest.raises(ValueError, match="spatial shape"):
        SourceImageObjectLabelBuildRequest(
            image=source, labels=np.ones((2, 5, 7), dtype=np.int32),
            plane_projection=projection,
        ).payload()


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
    source = _source(labels)
    projection = RuntimePlaneAxisValueProjection.from_source_declaration(
        source.metadata.plane_axis, source.metadata.source_provenance,
    )
    value = CalibratedSavedLabels(
        image=source, labels=labels, plane_projection=projection,
    ).payload()
    assert value.domain.scope is ObjectLabelDomainScope.PLANE
    assert len(value.measurement_planes()) == 2
    with pytest.raises(ValueError, match="Physical scalar pixel size requires"):
        CalibratedSavedLabels(image=_source(labels, spacing=()), labels=labels, plane_projection=projection).payload()
    assert _saved_label_input(_source(labels, spacing=())).domain.scope is ObjectLabelDomainScope.PLANE


class PairedSourceAdmission:
    """An independent declared requirement limiting a projection to two sources."""

    def __post_init__(self):
        super().__post_init__()
        if self.axis_size > 2:
            raise ValueError("Paired projection accepts at most two source planes.")


class PairedSourceProjection(PairedSourceAdmission, RuntimePlaneAxisValueProjection):
    """An independent projection leaf using the unchanged source constructor."""


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_source_constructor_admits_a_new_cooperative_projection_capability(axis):
    source = _source(np.ones((2, 6, 7), dtype=np.int32), axis=axis)
    value = PairedSourceProjection.from_source_declaration(axis, source.metadata.source_provenance)
    assert isinstance(value, PairedSourceProjection)
    assert value.axis is axis
    assert value.axis_size == 2
    assert value.selected_plane(1).require_plane_index() == 1
    bigger = _source(np.ones((3, 6, 7), dtype=np.int32), axis=axis)
    with pytest.raises(ValueError, match="at most two source planes"):
        PairedSourceProjection.from_source_declaration(axis, bigger.metadata.source_provenance)
    assert RuntimePlaneAxisValueProjection.from_source_declaration(axis, bigger.metadata.source_provenance).axis_size == 3
    # Absence is a declaration, not inferred from three source records.
    assert PairedSourceProjection.from_source_declaration(None, bigger.metadata.source_provenance) is None


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_produced_volume_global_object_domain_is_independent_of_source_plane_axis(axis):
    labels = np.ones((2, 6, 7), dtype=np.int32)
    source = _source(labels, axis=axis, spacing=(2.0, 1.3556, 1.3556))
    value = SourceImageObjectLabelBuildRequest(
        image=source,
        labels=labels,
        declared_object_count=2,
        declared_object_ids=(1, 2),
    ).payload()

    assert value.domain.scope is ObjectLabelDomainScope.PAYLOAD
    assert value.domain.declared_object_count == 2
    assert value.domain.declared_object_ids == (1, 2)
    assert value.domain.declared_object_id_domains == ()
    assert value.plane_axis is None
    assert len(value.measurement_planes()) == 1
    np.testing.assert_array_equal(value.measurement_planes()[0].labels, labels)
    assert value.source_provenance.identity() == source.metadata.source_provenance.identity()
    assert value.parent_image_source_voxel_spacing == source.metadata.source_voxel_spacing


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_produced_volume_without_explicit_ids_keeps_one_global_present_id_domain(axis):
    labels = np.zeros((2, 6, 7), dtype=np.int32)
    labels[0, 1:3, 2:4] = 29
    labels[1, 2:4, 3:5] = 106
    value = SourceImageObjectLabelBuildRequest(
        image=_source(labels, axis=axis, spacing=(2.0, 1.3556, 1.3556)),
        labels=labels,
    ).payload()

    assert value.domain.scope is ObjectLabelDomainScope.PAYLOAD
    assert value.domain.declared_object_ids == (29, 106)
    assert value.domain.declared_object_id_domains == ()
    assert value.plane_axis is None
    assert len(value.measurement_planes()) == 1


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_explicit_plane_domain_still_requires_projection_and_rejects_global_count(axis):
    labels = np.ones((2, 6, 7), dtype=np.int32)
    source = _source(labels, axis=axis)
    with pytest.raises(ValueError, match="requires an exact plane projection"):
        SourceImageObjectLabelBuildRequest(
            image=source, labels=labels, domain_scope=ObjectLabelDomainScope.PLANE,
        ).payload()
    projection = RuntimePlaneAxisValueProjection.from_source_declaration(
        source.metadata.plane_axis, source.metadata.source_provenance,
    )
    with pytest.raises(ValueError, match="per-plane domains"):
        SourceImageObjectLabelBuildRequest(
            image=source, labels=labels, domain_scope=ObjectLabelDomainScope.PLANE,
            plane_projection=projection, declared_object_count=1,
        ).payload()


@pytest.mark.parametrize("axis", tuple(RuntimePlaneAxis))
def test_generic_output_context_uses_execution_projection_not_image_storage_axis(axis):
    from openhcs.core.runtime_image_values import ImagePayload

    labels = np.zeros((2, 6, 7), dtype=np.int32)
    labels[0, 1:3, 2:4] = 29
    labels[1, 2:4, 3:5] = 106
    source = _source(labels, axis=axis, spacing=(2.0, 1.3556, 1.3556))
    volume = ImagePayload.of(labels).object_label_output(source, None)
    assert volume.domain.scope is ObjectLabelDomainScope.PAYLOAD
    assert volume.domain.declared_object_ids == (29, 106)
    np.testing.assert_array_equal(volume.measurement_planes()[0].labels, labels)
    projection = RuntimePlaneAxisValueProjection.from_source_declaration(
        source.metadata.plane_axis, source.metadata.source_provenance,
    )
    planes = ImagePayload.of(labels).object_label_output(source, projection)
    assert planes.domain.scope is ObjectLabelDomainScope.PLANE
    assert planes.domain.declared_object_id_domains == ((29,), (106,))
    assert planes.plane_axis is axis
    for index, plane in enumerate(planes.measurement_planes()):
        np.testing.assert_array_equal(plane.labels, labels[index])
    assert planes.source_provenance.identity() == volume.source_provenance.identity()


def test_saved_ingress_preserves_already_typed_object_domain_and_identity():
    labels = np.ones((2, 6, 7), dtype=np.int32)
    source = _source(labels, spacing=(2.0, 1.3556, 1.3556))
    produced = SourceImageObjectLabelBuildRequest(
        image=source, labels=labels, declared_object_count=1,
    ).label_set(name="saved_labels")
    admitted = _saved_label_input(produced)
    assert admitted is produced
    assert admitted.domain.scope is ObjectLabelDomainScope.PAYLOAD
    assert admitted.domain.declared_object_count == 1
    np.testing.assert_array_equal(admitted.measurement_planes()[0].labels, labels)
