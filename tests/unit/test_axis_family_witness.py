"""Witness: a second, non-microscopy family needs only its declaration.

A remote-sensing family (scene, tile, band, date; no stack axis) is declared
here and activated in-process. Family queries, configuration defaults and
validation, viewer mode projection, plane filenames and the compiler's
axis resolution all follow it without kernel edits.
"""

from __future__ import annotations

from collections.abc import Iterator

import pytest

from openhcs.core.axes import (
    Axis,
    AxisFamily,
    ColourAxis,
    DefaultGroupBy,
    DefaultVariable,
    LabelValued,
    OrdinalValued,
    PartitionAxis,
    StackAxis,
    TileAxis,
    TimeAxis,
    Ungrouped,
)
from openhcs.domains.microscopy.axes import Microscopy


class RemoteSensing(AxisFamily):
    class Tile(Axis, TileAxis, DefaultVariable, OrdinalValued):
        name = "tile"
        filename_prefix = "f"
        filename_padding = 3

    class Band(Axis, ColourAxis, DefaultGroupBy, OrdinalValued):
        name = "band"
        filename_prefix = "b"

    class Date(Axis, TimeAxis, OrdinalValued):
        name = "date"
        filename_prefix = "d"
        filename_padding = 3

    class Scene(Axis, PartitionAxis, LabelValued):
        name = "scene"


@pytest.fixture
def remote_sensing() -> Iterator[type[RemoteSensing]]:
    RemoteSensing.activate()
    try:
        yield RemoteSensing
    finally:
        Microscopy.activate()


def test_family_queries_follow_the_declaration(remote_sensing) -> None:
    family = AxisFamily.active()
    assert family is RemoteSensing
    assert family.partition_axis() is RemoteSensing.Scene
    assert family.variable_axes() == (
        RemoteSensing.Tile,
        RemoteSensing.Band,
        RemoteSensing.Date,
    )
    assert family.with_role(StackAxis) == ()
    assert family.default_variable() == (RemoteSensing.Tile,)
    assert family.default_group_by() is RemoteSensing.Band
    assert family.named("date") is RemoteSensing.Date
    assert family.grouping_named("none") is Ungrouped


def test_configuration_derives_from_the_active_family(remote_sensing) -> None:
    from openhcs.core.config import (
        FijiDisplayConfig,
        NapariDisplayConfig,
        ProcessingConfig,
        SequentialProcessingConfig,
    )

    config = ProcessingConfig()
    assert config.variable_components == [RemoteSensing.Tile]
    assert config.group_by is RemoteSensing.Band
    with pytest.raises(ValueError, match="variable_components"):
        ProcessingConfig(variable_components=[RemoteSensing.Scene])
    with pytest.raises(ValueError, match="sequential_components"):
        SequentialProcessingConfig(sequential_components=[Microscopy.Channel])

    fiji = FijiDisplayConfig()
    assert fiji.COMPONENT_ORDER == ("tile", "band", "date", "scene")
    assert fiji.component_modes() == {
        "tile": "frame",
        "band": "channel",
        "date": "frame",
        "scene": "frame",
    }
    assert set(NapariDisplayConfig().component_modes()) == set(RemoteSensing.names())
    payload = {"component_modes": fiji.component_modes(), "lut": "Grays", "auto_contrast": True}
    assert FijiDisplayConfig.from_display_payload(payload) == fiji


def test_plane_addresses_spell_the_declared_tokens(remote_sensing) -> None:
    from openhcs.core.source_projection import OpenHCSPlaneAddress

    parsed = OpenHCSPlaneAddress.from_filename("S07_f002_b3_d014.tif")
    assert parsed is not None
    assert parsed.address.value_for(RemoteSensing.Scene) == "S07"
    assert parsed.address.value_for(RemoteSensing.Band) == "3"
    assert parsed.address.filename(".tif") == "S07_f002_b3_d014.tif"


def test_step_validation_and_compiler_axis_resolution(remote_sensing) -> None:
    from openhcs.core.components.validation import GenericValidator
    from openhcs.core.pipeline.path_planner import (
        PathPlannerComponentScopes,
        PathPlannerExecutionGroups,
    )

    validator = GenericValidator(AxisFamily.active())
    assert validator.validate_step([RemoteSensing.Tile], RemoteSensing.Band, True, "s").is_valid
    rejected = validator.validate_step([RemoteSensing.Band], RemoteSensing.Band, True, "s")
    assert not rejected.is_valid
    partition = validator.validate_step([RemoteSensing.Scene], Ungrouped, False, "s")
    assert "multiprocessing axis: scene" in partition.error_message

    assert (
        PathPlannerComponentScopes.component_from_group_by(RemoteSensing.Date)
        is RemoteSensing.Date
    )
    assert PathPlannerComponentScopes.component_from_group_by(Ungrouped) is None
    assert (
        PathPlannerExecutionGroups.execution_component_for_dict_pattern(
            RemoteSensing.Band, "step"
        )
        is RemoteSensing.Band
    )
    with pytest.raises(ValueError, match="dict function pattern"):
        PathPlannerExecutionGroups.execution_component_for_dict_pattern(Ungrouped, "s")


def test_family_declaration_enforces_role_cardinality() -> None:
    with pytest.raises(TypeError, match="PartitionAxis"):

        class _TwoPartitions(AxisFamily):
            class A(Axis, PartitionAxis, LabelValued):
                name = "a"

            class B(Axis, PartitionAxis, LabelValued):
                name = "b"

    with pytest.raises(TypeError, match="exactly one PartitionAxis"):

        class _NoPartition(AxisFamily):
            class A(Axis, TileAxis, OrdinalValued):
                name = "a"

    with pytest.raises(TypeError, match="value kind|AxisValueKind"):

        class _NoKind(Axis, TileAxis):
            name = "x"

    # A rejected declaration must not leak into other axes' role checks.
    assert not issubclass(Microscopy.Channel, TileAxis)
    assert not issubclass(RemoteSensing.Band, PartitionAxis)
