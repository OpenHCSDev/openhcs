from __future__ import annotations

from abc import ABC
from collections.abc import Iterator

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import (
    AlignedImageStackKwargResolver,
    AlignedImageSliceContext,
    ImageOutputBundle,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCarrier,
    ImageMetadataPayload,
    image_payload_data,
)
from openhcs.core.runtime_object_labels import ObjectLabelSet, ObjectLabelVariantData
from openhcs.core.runtime_object_label_domains import ObjectLabelDomain, ObjectLabelDomainScope
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
    RuntimeSliceProjectableValue,
)
from openhcs.core.runtime_slice_alignment import RuntimeSliceAlignedValues
from openhcs.core.runtime_slice_projection import (
    RuntimeSliceProjection,
    RuntimeSliceProjectionDeclarationError,
    RuntimeSliceProjectionStrategy,
    ImagePayloadRuntimeSliceProjectionStrategy,
    SequenceRuntimeSliceProjectionStrategy,
)


def _clear_strategy_caches() -> None:
    RuntimeSliceProjectionStrategy.registered_strategy_types.cache_clear()
    RuntimeSliceProjectionStrategy.strategy_types_for_nominal_type.cache_clear()
    RuntimeSliceProjectionStrategy.strategy_types_for_aligned_kwarg_type.cache_clear()


@pytest.fixture
def isolated_strategy_registry() -> Iterator[dict[str, type[RuntimeSliceProjectionStrategy]]]:
    registry = RuntimeSliceProjectionStrategy.__registry__
    snapshot = registry.copy()
    _clear_strategy_caches()
    try:
        yield registry
    finally:
        registry.clear()
        registry.update(snapshot)
        _clear_strategy_caches()


def _resolver(*, axis=RuntimePlaneAxis.RUNTIME_SLICE, size=2, index=1):
    return AlignedImageStackKwargResolver(
        RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=axis, plane_index=index, axis_size=size,
        ),
    )


def test_dynamic_aligned_operation_registers_on_existing_projection_family(isolated_strategy_registry):
    class DynamicKwarg:
        pass

    marker = object()

    class DynamicProjectionStrategy(RuntimeSliceProjectionStrategy):
        value_type = DynamicKwarg

        def resolve_aligned_kwarg(self, value, resolver):
            assert isinstance(value, DynamicKwarg)
            assert resolver.projection_axis.axis_size == 2
            return marker

    assert DynamicProjectionStrategy.value_type_label is not None
    assert isolated_strategy_registry[DynamicProjectionStrategy.value_type_label] is DynamicProjectionStrategy
    assert _resolver().resolve(DynamicKwarg()) is marker


def test_aligned_operation_follows_exact_value_mro(isolated_strategy_registry):
    class BaseKwarg:
        pass

    class DerivedKwarg(BaseKwarg):
        pass

    class MostDerivedKwarg(DerivedKwarg):
        pass

    base_marker, derived_marker = object(), object()

    class BaseProjectionStrategy(RuntimeSliceProjectionStrategy):
        value_type = BaseKwarg

        def resolve_aligned_kwarg(self, value, resolver):
            return base_marker

    class DerivedProjectionStrategy(BaseProjectionStrategy):
        value_type = DerivedKwarg

        def resolve_aligned_kwarg(self, value, resolver):
            return derived_marker

    assert RuntimeSliceProjectionStrategy.strategy_types_for_aligned_kwarg_type(MostDerivedKwarg) == (
        DerivedProjectionStrategy, BaseProjectionStrategy,
    )
    assert _resolver().resolve(MostDerivedKwarg()) is derived_marker


def test_default_aligned_hook_does_not_steal_projectable_operation_through_mi(isolated_strategy_registry):
    class OrdinaryOwner:
        pass

    class MixedKwarg(OrdinaryOwner, RuntimeSliceProjectableValue):
        def project_runtime_slice(self, slice_index):
            pytest.fail("ordinary nominal owner must determine the inner projection")

    marker = object()

    class OrdinaryOnlyProjectionStrategy(RuntimeSliceProjectionStrategy):
        value_type = OrdinaryOwner

        def value_for_slice(self, value, context):
            assert isinstance(value, MixedKwarg)
            assert context.require_plane_index() == 1
            return marker

    ordinary = RuntimeSliceProjectionStrategy.strategy_types_for_nominal_type(MixedKwarg)
    aligned = RuntimeSliceProjectionStrategy.strategy_types_for_aligned_kwarg_type(MixedKwarg)
    assert ordinary[0] is OrdinaryOnlyProjectionStrategy
    assert OrdinaryOnlyProjectionStrategy not in aligned
    assert _resolver().resolve(MixedKwarg()) is marker


def test_virtual_abc_ties_follow_single_canonical_registry_order(isolated_strategy_registry):
    class FirstMember(ABC):
        pass

    class SecondMember(ABC):
        pass

    class VirtualValue:
        pass

    FirstMember.register(VirtualValue)
    SecondMember.register(VirtualValue)
    first, second = object(), object()

    class FirstProjectionStrategy(RuntimeSliceProjectionStrategy):
        value_type = FirstMember

        def value_for_slice(self, value, context):
            return first

        def resolve_aligned_kwarg(self, value, resolver):
            return first

    class SecondProjectionStrategy(RuntimeSliceProjectionStrategy):
        value_type = SecondMember

        def value_for_slice(self, value, context):
            return second

        def resolve_aligned_kwarg(self, value, resolver):
            return second

    value, resolver = VirtualValue(), _resolver()
    assert resolver.resolve(value) is first
    assert RuntimeSliceProjection.value_for_slice(value, resolver.projection_axis) is first
    key = FirstProjectionStrategy.value_type_label
    isolated_strategy_registry[key] = isolated_strategy_registry.pop(key)
    _clear_strategy_caches()
    assert resolver.resolve(value) is second
    assert RuntimeSliceProjection.value_for_slice(value, resolver.projection_axis) is second


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
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="no nominal strategy"):
        RuntimeSliceProjection.value_for_slice(value, _resolver().projection_axis)


def test_broad_image_carrier_aligned_operation_preserves_declared_stack():
    class BroadCarrier(ImagePayloadMetadataCarrier):
        def __init__(self):
            self.pixels = np.ones((2, 3, 4), dtype=np.float32)
            self._metadata = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE)

        def image_data(self):
            return self.pixels

        @property
        def metadata(self):
            return self._metadata

    value = BroadCarrier()
    assert _resolver().resolve(value) is value
    assert value.image_data().shape == (2, 3, 4)
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="no nominal strategy"):
        RuntimeSliceProjection.value_for_slice(value, _resolver().projection_axis)


def test_image_aligned_operation_does_not_remove_runtime_plane_axis():
    value = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(
        np.arange(24, dtype=np.float32).reshape(2, 3, 4),
    )
    resolver = _resolver()
    assert resolver.resolve(value) is value
    ordinary = RuntimeSliceProjection.value_for_slice(value, resolver.projection_axis)
    np.testing.assert_array_equal(image_payload_data(ordinary), image_payload_data(value)[1])
    assert image_payload_data(ordinary).shape == (3, 4)


def test_image_output_bundle_aligned_operation_selects_outer_member_then_recurses():
    first, second = tuple(
        ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(
            np.full((2, 3, 4), index, dtype=np.float32),
        ) for index in (1, 2)
    )
    bundle = ImageOutputBundle(
        (first, second),
        tuple(AlignedImageSliceContext.independent_main_flow(name) for name in ("First", "Second")),
    )
    resolver = _resolver()
    assert resolver.resolve(bundle) is second
    assert image_payload_data(resolver.resolve(bundle)).shape == (2, 3, 4)
    ordinary = RuntimeSliceProjection.value_for_slice(bundle, resolver.projection_axis)
    assert isinstance(ordinary, ImageOutputBundle)
    assert [image_payload_data(value).shape for value in ordinary.slices] == [(3, 4), (3, 4)]


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


def test_narrower_image_owner_inherits_operation_scope_from_its_own_declaration(isolated_strategy_registry):
    class DerivedImage(ImageMetadataPayload):
        pass

    marker = object()

    class DerivedImageProjectionStrategy(ImagePayloadRuntimeSliceProjectionStrategy):
        value_type = DerivedImage

        def resolve_aligned_kwarg(self, value, resolver):
            return marker

    value = DerivedImage(
        data=np.arange(24, dtype=np.float32).reshape(2, 3, 4),
        metadata=ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE),
    )
    assert RuntimeSliceProjectionStrategy.strategy_types_for_aligned_kwarg_type(DerivedImage)[0] is DerivedImageProjectionStrategy
    assert RuntimeSliceProjectionStrategy.strategy_types_for_nominal_type(DerivedImage)[0] is DerivedImageProjectionStrategy
    assert _resolver().resolve(value) is marker
    ordinary = RuntimeSliceProjection.value_for_slice(value, _resolver().projection_axis)
    np.testing.assert_array_equal(image_payload_data(ordinary), value.data[1])


def test_narrower_sequence_owner_can_declare_aligned_list_capability(isolated_strategy_registry):
    class DeclaredList(list):
        pass

    class DeclaredListProjectionStrategy(SequenceRuntimeSliceProjectionStrategy):
        value_type = DeclaredList

    resolver = _resolver()
    projection = resolver.projection_axis
    original = DeclaredList([projection, object()])
    assert RuntimeSliceProjectionStrategy.strategy_types_for_aligned_kwarg_type(DeclaredList)[0] is DeclaredListProjectionStrategy
    aligned = resolver.resolve(original)
    assert isinstance(aligned, tuple)
    assert aligned[0].require_plane_index() == 1
    assert aligned[1] is original[1]
    plain = list(original)
    assert resolver.resolve(plain) is plain


def test_derived_dispatch_cache_uses_the_same_explicit_registry_mutation_boundary(isolated_strategy_registry):
    class DynamicKwarg:
        pass

    resolver, value = _resolver(), DynamicKwarg()
    assert resolver.resolve(value) is value
    marker = object()

    class DynamicProjectionStrategy(RuntimeSliceProjectionStrategy):
        value_type = DynamicKwarg

        def resolve_aligned_kwarg(self, value, resolver):
            return marker

    _clear_strategy_caches()
    assert resolver.resolve(value) is marker
    before = RuntimeSliceProjectionStrategy.strategy_types_for_aligned_kwarg_type.cache_info()
    assert resolver.resolve(value) is marker
    after = RuntimeSliceProjectionStrategy.strategy_types_for_aligned_kwarg_type.cache_info()
    assert after.hits == before.hits + 1
