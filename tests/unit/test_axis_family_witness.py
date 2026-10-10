"""Witness: a second, non-microscopy family needs only its declaration.

A remote-sensing family (scene, tile, band, date; no stack axis) is declared
here and activated in-process. Family queries, configuration defaults and
validation, viewer mode projection, plane filenames and the compiler's
axis resolution all follow it without kernel edits. In a fresh process the
same family opens a dataset written in the kernel's openhcsdata format and
runs a two-step pipeline end to end.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from collections.abc import Iterator
from pathlib import Path

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
    payload_spatial_rank = 2

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


def test_pipeline_runs_end_to_end_through_the_kernel_dataset_source(tmp_path) -> None:
    script = Path(__file__).with_name("remote_sensing_witness_pipeline.py")
    repo_root = Path(__file__).resolve().parents[2]
    completed = subprocess.run(
        [sys.executable, str(script), str(tmp_path)],
        capture_output=True,
        text=True,
        timeout=600,
        env={**os.environ, "PYTHONPATH": str(repo_root)},
        check=False,
    )
    assert completed.returncode == 0, completed.stderr[-4000:]
    report = json.loads(completed.stdout.strip().splitlines()[-1])

    assert report["is_kernel_source"], report["source_type"]
    assert report["results"] == {"S01": True, "S02": True}, report["errors"]
    assert report["outputs"] == sorted(
        f"images/{scene}_f{int(tile):03d}_b{band}_d{int(date):03d}.tif"
        for scene in ("S01", "S02")
        for tile in ("1", "2")
        for band in ("1", "2")
        for date in ("1", "2", "3")
    )
    assert set(report["output_maxima"].values()) == {500}
    written = set(report["output_subdirectories"]["images"])
    assert {"scenes", "tiles", "bands", "dates"} <= written
    assert not written & {"wells", "sites", "channels", "z_indexes", "timepoints"}
    assert report["output_band_labels"] == {"1": "red", "2": "nir"}
    assert not {"analysis_consolidation_config", "plate_metadata_config"} & set(
        report["config_fields"]
    )
    assert report["loaded_domain_modules"] == []


# ---------------------------------------------------------------------------
# A non-image family flows through the tensor payload layer
# ---------------------------------------------------------------------------


class Telemetry(AxisFamily):
    """Sensor stations recording 1-D time series; values have no spatial axes."""

    payload_spatial_rank = 0

    class Window(Axis, TileAxis, DefaultVariable, OrdinalValued):
        name = "window"

    class Sensor(Axis, ColourAxis, DefaultGroupBy, OrdinalValued):
        name = "sensor"

    class Time(Axis, TimeAxis, OrdinalValued):
        name = "time"

    class Station(Axis, PartitionAxis, LabelValued):
        name = "station"


@pytest.fixture
def telemetry() -> Iterator[type[Telemetry]]:
    Telemetry.activate()
    try:
        yield Telemetry
    finally:
        Microscopy.activate()


def _signal(offset: float):
    import numpy as np

    from openhcs.core.payload_axes import FamilyAxisSpec, PayloadAxes
    from openhcs.core.runtime_image_values import ImagePayloadMetadata

    metadata = ImagePayloadMetadata(
        source_dtype="float32",
        axes=PayloadAxes.of(
            (FamilyAxisSpec(Telemetry.Sensor), 0),
            (FamilyAxisSpec(Telemetry.Time), -1),
        ),
    )
    samples = np.arange(12, dtype=np.float32).reshape(3, 4) + offset
    return metadata.payload_with(samples)


def test_time_series_payloads_declare_their_axes(telemetry) -> None:
    import numpy as np

    from openhcs.core.payload_axes import (
        FamilyAxisSpec,
        SpatialAxis,
        UndeclaredAxisSpec,
    )
    from openhcs.core.runtime_image_values import ImagePayload
    from openhcs.core.source_spatial_domain import PointSourceSpatialDomain

    signal = _signal(0.0)
    assert signal.axes == (
        FamilyAxisSpec(Telemetry.Sensor),
        FamilyAxisSpec(Telemetry.Time),
    )
    assert signal.metadata.axis_index(TimeAxis, signal) == 1
    assert signal.metadata.axis_index(ColourAxis, signal) == 0
    assert type(signal.metadata.source_spatial_domain) is PointSourceSpatialDomain
    assert signal.metadata.spatial_axes(signal) == ()
    assert signal.metadata.spatial_axes_yx(signal) is None
    assert not any(spec.has_role(SpatialAxis) for spec in signal.axes)

    # The family declares no spatial axes, so nothing in a bare array is spatial.
    bare = ImagePayload.of(np.zeros(5, dtype=np.float32))
    assert bare.axes == (UndeclaredAxisSpec(),)


def test_time_series_stack_slices_and_projects_without_kernel_edits(telemetry) -> None:
    import numpy as np

    from openhcs.core.aligned_image_payload import stack_image_payloads
    from openhcs.core.payload_axes import FamilyAxisSpec, RuntimePlaneAxisSpec
    from openhcs.core.runtime_image_values import (
        ImagePayloadMetadata,
        ImagePayloadMetadataCompositionMode,
        MaskedImagePayload,
    )
    from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
    from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

    signals = (_signal(0.0), _signal(100.0))
    stack = stack_image_payloads(
        signals, metadata_mode=ImagePayloadMetadataCompositionMode.STACK
    )
    assert stack.geometry.shape == (2, 3, 4)
    assert stack.axes == (
        RuntimePlaneAxisSpec(RuntimePlaneAxis.RUNTIME_SLICE.value),
        FamilyAxisSpec(Telemetry.Sensor),
        FamilyAxisSpec(Telemetry.Time),
    )
    assert RuntimeSliceProjection.slice_count_from_values((stack,)) == 2

    slices = stack.alignment_slices()
    assert len(slices) == 2
    for original, projected in zip(signals, slices, strict=True):
        np.testing.assert_array_equal(np.asarray(projected.data), original.data)
        assert projected.axes == original.axes
        assert projected.metadata.plane_axis is None

    restored = ImagePayloadMetadata.from_mapping(
        {"axes": stack.metadata.axes.to_mapping(), "source_dtype": "float32"}
    )
    assert restored.axes == stack.metadata.axes

    # A mask may omit the declared non-spatial axes and broadcasts over them.
    masked = MaskedImagePayload(
        data=signals[0].data,
        mask=np.ones((3, 4), dtype=bool),
        metadata=signals[0].metadata,
    )
    assert masked.metadata.mask_domain(masked).accepts((3, 4))
    without_time = masked.metadata.without_axis(TimeAxis)
    assert without_time.axis_index(TimeAxis, masked) is None
    assert without_time.axis_index(ColourAxis, masked) == 0
