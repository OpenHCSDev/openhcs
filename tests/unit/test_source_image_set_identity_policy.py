"""Field identity derives from binding coordinates, not selected plane paths."""

import pytest

from openhcs.constants.constants import AllComponents, GroupBy
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.source_bindings import (
    ComponentSelector,
    NamedSourceBinding,
    SourceBindingsConfig,
    SourceSelector,
)
from openhcs.core.source_image_provenance import SourceImageProvenance
from openhcs.core.source_matching import (
    SourceImageSetIdentity,
    SourceImageSetIdentityPolicy,
)
from openhcs.interop.cellprofiler.image_set_numbering import (
    CellProfilerImageSetNumbering,
)


def _bindings(*, stack=(), selectors=False):
    return SourceBindingsConfig(
        source_stack_components=stack,
        bindings=tuple(
            NamedSourceBinding(
                alias=f"Plane{channel}",
                selector=SourceSelector(components=coordinates)
                if selectors
                else SourceSelector(),
                component_identity=() if selectors else coordinates,
            )
            for channel in ("1", "2", "3")
            for coordinates in (
                tuple(
                    ComponentSelector(component, value)
                    for component, value in (
                        (AllComponents.WELL, "A01"),
                        (AllComponents.SITE, "1"),
                        (AllComponents.CHANNEL, channel),
                        (AllComponents.Z_INDEX, "1"),
                        (AllComponents.TIMEPOINT, "1"),
                    )
                ),
            )
        ),
    )


@pytest.mark.parametrize("selectors", (False, True))
def test_shared_binding_coordinates_remain_field_axes(selectors):
    policy = SourceImageSetIdentityPolicy.from_source_bindings(
        _bindings(selectors=selectors)
    )

    assert policy.plane_member_components == frozenset((AllComponents.CHANNEL,))


@pytest.mark.parametrize(
    "component", (AllComponents.SITE, AllComponents.Z_INDEX, AllComponents.TIMEPOINT)
)
def test_explicit_stack_and_group_axes_override_shared_coordinates(component):
    for policy in (
        SourceImageSetIdentityPolicy.from_source_bindings(
            _bindings(stack=(component,))
        ),
        SourceImageSetIdentityPolicy.from_source_bindings(
            _bindings(), group_component=component
        ),
    ):
        assert policy.plane_member_components == frozenset(
            (AllComponents.CHANNEL, component)
        )


@pytest.mark.parametrize(
    "component",
    (
        AllComponents.WELL,
        AllComponents.SITE,
        AllComponents.Z_INDEX,
        AllComponents.TIMEPOINT,
    ),
)
def test_numbering_combines_channels_but_preserves_independent_fields(component):
    policy = SourceImageSetIdentityPolicy.from_source_bindings(_bindings())
    numbering = CellProfilerImageSetNumbering(policy)
    scope = RuntimeExecutionAxisScope.from_raw(
        "A01", component=AllComponents.CHANNEL, value="1"
    )
    metadata = {
        "well": "A01",
        "site": "1",
        "channel": "1",
        "z_index": "1",
        "timepoint": "1",
    }
    numbers = []
    for field_value in ("1", "2"):
        for channel in ("1", "2", "3"):
            provenance = SourceImageProvenance(
                source_path=f"/synthetic/field-{field_value}-plane-{channel}.tif",
                source_component_metadata={
                    **metadata,
                    component.value: field_value,
                    "channel": channel,
                },
            )
            numbers.append(
                numbering.for_source_slice(
                    scope=scope, provenance=provenance, slice_index=0, owner="Cells"
                )
            )

    assert numbers == [1, 1, 1, 2, 2, 2]


def test_component_assignment_owns_identity_over_physical_selector():
    declarations = SourceBindingsConfig(
        bindings=tuple(
            NamedSourceBinding(
                alias=f"Plane{channel}",
                selector=SourceSelector(
                    components=(ComponentSelector(AllComponents.SITE, physical_site),)
                ),
                component_identity=(
                    ComponentSelector(AllComponents.SITE, "1"),
                    ComponentSelector(AllComponents.CHANNEL, channel),
                ),
            )
            for channel, physical_site in (("1", "7"), ("2", "8"))
        )
    )
    policy = SourceImageSetIdentityPolicy.from_source_bindings(declarations)

    assert policy.plane_member_components == frozenset((AllComponents.CHANNEL,))


def test_path_identity_stays_distinct_without_semantic_field_coordinates():
    policy = SourceImageSetIdentityPolicy.from_source_bindings(_bindings())

    assert SourceImageSetIdentity.from_metadata(
        {}, fallback_source_path="/synthetic/one.tif", policy=policy
    ) != SourceImageSetIdentity.from_metadata(
        {}, fallback_source_path="/synthetic/two.tif", policy=policy
    )


def test_pipeline_config_compiles_the_same_paired_field_identity_policy():
    from openhcs.core.config import (
        LazyProcessingConfig,
        LazySourceBindingsConfig,
        PipelineConfig,
    )

    config = PipelineConfig(
        processing_config=LazyProcessingConfig(group_by=GroupBy.CHANNEL),
        source_bindings_config=LazySourceBindingsConfig(bindings=_bindings().bindings),
    )

    policy = SourceImageSetIdentityPolicy.from_pipeline_config(config)

    assert policy.plane_member_components == frozenset((AllComponents.CHANNEL,))
