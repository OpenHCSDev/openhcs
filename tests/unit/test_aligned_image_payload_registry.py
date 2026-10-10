from __future__ import annotations


import numpy as np
import pytest

from openhcs.core.aligned_image_payload import (
    AlignedImageStackKwargResolver,
    AlignedImageSliceContext,
    ImageOutputBundle,
    ProducedImageStack,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
)
from openhcs.core.runtime_object_labels import ObjectLabelSet, ObjectLabelVariantData
from openhcs.core.runtime_object_label_domains import ObjectLabelDomain, ObjectLabelDomainScope
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.runtime_slice_projection import (
    RuntimeSliceProjection,
    RuntimeSliceProjectionDeclarationError,
)


def _resolver(*, axis=RuntimePlaneAxis.RUNTIME_SLICE, size=2, index=1):
    return AlignedImageStackKwargResolver(
        RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=axis, plane_index=index, axis_size=size,
        ),
    )


def test_tuple_recurses_while_list_stays_in_its_original_domain():
    projection = _resolver().projection_axis
    elements = [object(), object()]
    # A projection declaration has its own meaningful projectable capability.
    values = (projection, elements)
    result = _resolver().resolve(values)
    assert type(result) is tuple
    assert result[0].require_plane_index() == 1
    assert result[1] is elements
    assert _resolver().resolve(elements) is elements


def test_unknown_aligned_value_passes_through_but_ordinary_projection_stays_strict():
    class Unknown:
        pass

    value = Unknown()
    assert _resolver().resolve(value) is value
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="has no declaration"):
        RuntimeSliceProjection.value_for_slice(value, _resolver().projection_axis)


def test_image_aligned_operation_does_not_remove_runtime_plane_axis():
    value = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(
        np.arange(24, dtype=np.float32).reshape(2, 3, 4),
    )
    resolver = _resolver()
    assert resolver.resolve(value) is value
    ordinary = RuntimeSliceProjection.value_for_slice(value, resolver.projection_axis)
    np.testing.assert_array_equal(ordinary.data, value.data[1])
    assert ordinary.data.shape == (3, 4)


@pytest.mark.parametrize("axis", (RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING))
def test_produced_literal_stack_uses_image_aligned_operation_without_selecting_a_plane(axis):
    value = ProducedImageStack(
        tuple(np.full((3, 4), index, dtype=np.float32) for index in (1, 2, 3)),
        memory_type="numpy", plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    assert _resolver(axis=axis).resolve(value) is value
    assert value._composed_payload is None


@pytest.mark.parametrize("inner_count", (1, 2, 3))
@pytest.mark.parametrize("axis", (RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING))
def test_image_output_bundle_aligned_operation_selects_outer_member_then_recurses(inner_count, axis):
    first, second = tuple(
        ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(
            np.full((inner_count, 3, 4), index, dtype=np.float32),
        ) for index in (1, 2)
    )
    bundle = ImageOutputBundle(
        (first, second),
        tuple(AlignedImageSliceContext.independent_main_flow(name) for name in ("First", "Second")),
    )
    resolver = _resolver(axis=axis)
    assert resolver.resolve(bundle) is second
    assert resolver.resolve(bundle).data.shape == (inner_count, 3, 4)
    ordinary = RuntimeSliceProjection.value_for_slice(
        bundle, _resolver(size=inner_count, index=0).projection_axis,
    )
    assert isinstance(ordinary, ImageOutputBundle)
    assert [value.data.shape for value in ordinary.slices] == [(3, 4), (3, 4)]


def test_image_output_bundle_aligned_operation_checks_outer_cardinality_before_inner_planes():
    value = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(
        np.ones((3, 3, 4), dtype=np.float32),
    )
    bundle = ImageOutputBundle(
        (value, value),
        tuple(AlignedImageSliceContext.independent_main_flow(name) for name in ("First", "Second")),
    )
    with pytest.raises(ValueError, match="Nested aligned image stack cardinality"):
        _resolver(size=3).resolve(bundle)


def test_image_output_bundle_aligned_operation_recurses_through_selected_bundle():
    values = tuple(
        ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(
            np.full((3, 3, 4), index, dtype=np.float32),
        ) for index in (1, 2)
    )
    contexts = tuple(
        AlignedImageSliceContext.independent_main_flow(name) for name in ("First", "Second")
    )
    inner = ImageOutputBundle(values, contexts)
    outer = ImageOutputBundle((values[0], inner), contexts)
    assert _resolver().resolve(outer) is values[1]


@pytest.mark.parametrize("axis", (RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING))
def test_aligned_capability_owns_outer_count_for_both_declared_axes(axis):
    first, second = object(), object()
    value = RuntimeSliceAlignedValues((first, second))
    resolver = _resolver(axis=axis)
    assert resolver.resolve(value) is second
    if axis is RuntimePlaneAxis.SOURCE_BINDING:
        assert RuntimeSliceProjection.value_for_slice(value, resolver.projection_axis) is value
    with pytest.raises(ValueError, match="count must exactly match"):
        _resolver(axis=axis, size=3).resolve(value)


def test_object_label_count_is_checked_before_projection_and_spatial_alignment(monkeypatch):
    labels = ObjectLabelSet(
        name="Labels", variant_data=ObjectLabelVariantData(labels=np.ones((2, 3, 4), dtype=np.int32)),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        domain=ObjectLabelDomain(
            declared_object_id_domains=((1,), (1,)),
            scope=ObjectLabelDomainScope.PLANE,
        ),
    )
    monkeypatch.setattr(RuntimeSliceProjection, "value_for_slice", lambda *_args: pytest.fail("cardinality comes first"))
    monkeypatch.setattr(AlignedImageStackKwargResolver, "resolve_source_spatial_value", lambda *_args: pytest.fail("cardinality comes before spatial alignment"))
    with pytest.raises(ValueError, match="cardinality must exactly match"):
        _resolver(size=3).resolve(labels)


