"""Complete source-coordinate projection from the original runtime scope owner."""
from copy import deepcopy

import pytest

from openhcs.constants import AllComponents
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.source_matching import source_component_metadata_value


@pytest.mark.parametrize("grouped,fixed", [(False, False), (True, False), (False, True), (True, True)])
def test_scope_projects_every_owned_coordinate_without_inventing_absent_axes(grouped, fixed):
    scope = RuntimeExecutionAxisScope.from_raw(
        "A01",
        component=AllComponents.CHANNEL if grouped else None,
        value="2" if grouped else None,
        fixed_component_values=(
            ((AllComponents.SITE, "3"), (AllComponents.TIMEPOINT, "4")) if fixed else ()
        ),
    )
    original = {"source_alias": "Synthetic", "custom": {"retained": "value"}}
    untouched = deepcopy(original)
    metadata = scope.source_component_metadata(original)
    for component, value in scope.source_component_values:
        assert source_component_metadata_value(metadata, component) == value
    assert source_component_metadata_value(metadata, AllComponents.Z_INDEX) is None
    assert metadata["source_alias"] == "Synthetic"
    assert metadata["custom"] == original["custom"]
    assert original == untouched


@pytest.mark.parametrize("component,wrong", [
    (AllComponents.WELL, "B01"),
    (AllComponents.SITE, "8"),
    (AllComponents.TIMEPOINT, "7"),
])
def test_scope_rejects_conflicting_axis_and_fixed_identity(component, wrong):
    scope = RuntimeExecutionAxisScope.from_raw(
        "A01", component=AllComponents.CHANNEL, value="2",
        fixed_component_values=((AllComponents.SITE, "3"), (AllComponents.TIMEPOINT, "4")),
    )
    metadata = {component.value: wrong, "custom": "retained"}
    untouched = dict(metadata)
    with pytest.raises(ValueError, match="Runtime execution scope conflicts"):
        scope.source_component_metadata(metadata)
    assert metadata == untouched


def test_scope_canonicalizes_matching_component_alias_without_losing_source_fields():
    scope = RuntimeExecutionAxisScope.from_raw(
        "A01", component=AllComponents.CHANNEL, value="2",
        fixed_component_values=((AllComponents.SITE, "3"),),
    )
    metadata = scope.source_component_metadata({"Well": "A01", "Channel": "2", "custom": "retained"})
    assert source_component_metadata_value(metadata, AllComponents.CHANNEL) == "2"
    assert metadata["custom"] == "retained"


@pytest.mark.parametrize("fixed", [False, True])
def test_scope_keeps_measured_source_channel_distinct_from_object_group(fixed):
    scope = RuntimeExecutionAxisScope.from_raw(
        "A01", component=AllComponents.CHANNEL, value="2",
        fixed_component_values=((AllComponents.Z_INDEX, "1"),) if fixed else (),
    )
    metadata = scope.source_component_metadata({"channel": "1", "custom": "retained"})
    assert source_component_metadata_value(metadata, AllComponents.CHANNEL) == "1"
    assert scope.value_text_for_component(AllComponents.CHANNEL) == "2"
    assert metadata["custom"] == "retained"


def test_scope_still_rejects_a_contradictory_declared_group_coordinate():
    scope = RuntimeExecutionAxisScope.from_raw(
        "A01", component=AllComponents.CHANNEL, value="2",
        fixed_component_values=((AllComponents.Z_INDEX, "1"),),
    )
    with pytest.raises(ValueError, match="group coordinate conflicts"):
        scope.for_group_coordinate(AllComponents.CHANNEL, "3")
