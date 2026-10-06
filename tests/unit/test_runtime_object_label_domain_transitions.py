import numpy as np
import pytest

from openhcs.core.runtime_object_label_domains import (
    ObjectLabelDomain,
    ObjectLabelDomainScope,
    PresentObjectLabelIdsDomainDeclaration,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelSet,
    ObjectLabelVariantData,
    object_label_value_with_dense_labels,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCompositionMode,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import (
    RuntimeSourceImageProvenancePlane,
    SourceImageIdentity,
    SourceImageProvenance,
    SourceImageProvenancePlanes,
)


def test_payload_domain_replacement_drops_inherited_plane_axis() -> None:
    labels = np.asarray(
        (
            ((0, 1), (0, 0)),
            ((0, 1), (0, 2)),
        ),
        dtype=np.int32,
    )
    source = ObjectLabelSet(
        name="erodedDownsizedNuclei",
        variant_data=ObjectLabelVariantData(labels=labels),
        domain=ObjectLabelDomain.declared(
            scope=ObjectLabelDomainScope.PLANE,
            declared_object_id_domains=((1,), (1, 2)),
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )

    transformed = object_label_value_with_dense_labels(
        source,
        labels.copy(),
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )

    assert transformed.domain == ObjectLabelDomain.declared(
        scope=ObjectLabelDomainScope.PAYLOAD,
        declared_object_ids=(1, 2),
    )
    assert transformed.plane_axis is None
    np.testing.assert_array_equal(transformed.labels, labels)


def test_explicit_payload_domain_plane_axis_remains_invalid() -> None:
    with pytest.raises(
        ValueError,
        match="payload-scoped labels cannot declare a plane axis",
    ):
        ObjectLabelSet(
            name="invalid",
            variant_data=ObjectLabelVariantData(
                labels=np.zeros((2, 2, 2), dtype=np.int32)
            ),
            domain=ObjectLabelDomain.declared(
                scope=ObjectLabelDomainScope.PAYLOAD,
                declared_object_count=0,
            ),
            plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        )


def test_payload_measurement_reference_keeps_volume_planes_as_contributors() -> None:
    source_planes = SourceImageProvenancePlanes(
        tuple(
            RuntimeSourceImageProvenancePlane(
                SourceImageIdentity(f"/plate/A01_z{index:03d}.tif"),
                source_image_name="MembFinal",
            )
            for index in range(3)
        )
    )
    labels = ObjectLabelSet(
        name="Cells",
        variant_data=ObjectLabelVariantData(labels=np.zeros((3, 4, 5), dtype=np.int32)),
        source_provenance=SourceImageProvenance(
            source_image_provenance_planes=source_planes,
            source_image_names=("MembFinal",) * 3,
        ),
        domain=ObjectLabelDomain.declared(
            scope=ObjectLabelDomainScope.PAYLOAD,
            declared_object_count=0,
        ),
    )

    reference_image = labels.measurement_reference_image()
    reference_metadata = reference_image.metadata

    assert reference_metadata.plane_axis is None
    assert reference_metadata.source_provenance.source_plane_count == 0
    assert reference_metadata.source_image_provenance_planes.contributor_count == 3
    assert reference_metadata.source_image_names == ()
    assert reference_metadata.source_provenance.represented_source_image_names == (
        "MembFinal",
    )
    composed = ImagePayloadMetadata.compose(
        (reference_image,),
        mode=ImagePayloadMetadataCompositionMode.BUNDLE,
    )
    assert composed.source_provenance.represented_source_image_names == ("MembFinal",)


@pytest.mark.parametrize("axis", [RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING])
@pytest.mark.parametrize("plane_count", [1, 2])
def test_sparse_label_slice_projection_preserves_overlap_and_axis_domain(
    monkeypatch, axis, plane_count
):
    from openhcs.core.runtime_object_labels import (
        ObjectLabelRepresentation, SparseIJVObjectLabelStorageStrategy,
    )
    from openhcs.core.runtime_sparse_labels import SparseIJVLabelRows
    from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    first = SparseIJVLabelRows(np.asarray([[0, 1, 1], [0, 1, 2]], dtype=np.int32))
    planes = (first,) if plane_count == 1 else (
        first, SparseIJVLabelRows(np.asarray([[1, 0, 3]], dtype=np.int32)),
    )
    labels = ObjectLabelSet(
        name="OverlappingObjects",
        variant_data=ObjectLabelVariantData(SparseIJVLabelRows.from_slices(planes)),
        representation=ObjectLabelRepresentation.SPARSE_IJV,
        domain=ObjectLabelDomain(
            declared_object_id_domains=((1, 2),) if plane_count == 1 else ((1, 2), (3,)),
            scope=ObjectLabelDomainScope.PLANE,
        ),
        plane_axis=axis,
    )
    def reject_dense(*args, **kwargs):
        raise AssertionError("Slice projection must preserve sparse overlap")
    monkeypatch.setattr(SparseIJVObjectLabelStorageStrategy, "dense_data", reject_dense)
    preserved = RuntimePlaneAxisValueProjection.preserve(
        axis=axis, axis_size=plane_count,
    )
    projected = RuntimeSliceProjection.value_for_slice(labels, preserved.selected_plane(0))
    assert projected.plane_axis is None
    assert projected.domain.declared_object_ids == (1, 2)
    np.testing.assert_array_equal(projected.labels.as_array(), first.as_array())
    assert labels.plane_axis is axis
    with pytest.raises(ValueError, match="cardinality mismatch"):
        RuntimeSliceProjection.value_for_slice(
            labels,
            RuntimePlaneAxisValueProjection.from_selected_plane(
                axis=axis, axis_size=plane_count + 1, plane_index=0,
            ),
        )
    with pytest.raises(ValueError, match="plane_index must be within"):
        RuntimeSliceProjection.value_for_slice(labels, preserved.selected_plane(plane_count))
    with pytest.raises(ValueError, match="sparse label storage carries"):
        labels.with_variants(
            ObjectLabelVariantData(SparseIJVLabelRows.from_slices((*planes, first))),
        )
