from dataclasses import fields
from inspect import signature

import numpy as np
import pytest
import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from scipy import ndimage as ndi
from skimage.draw import disk, line

from openhcs.core.artifacts import (
    ArtifactSidecarRole,
    ArtifactViewerStreaming,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    SpatialGraphArtifactType,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelVariantData,
    object_label_dense_array,
)
from openhcs.core.runtime_spatial_graph import SpatialGraph
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    CELLPROFILER_NEURITE_ENGINE_PROFILE,
    NEURITE_OBJECT_LABEL_MATERIALIZATION,
    MetaXpressCellBodySettings,
    MetaXpressNuclearSettings,
    MetaXpressOutgrowthSettings,
    NeuriteIllumination,
    _adopt_secondary_owned_path_segments,
    _analyze_owned_topology,
    _analyze_topology,
    _build_neurite_morphology_graph,
    _cell_body_contract_candidates,
    _derive_signal_cell_bodies,
    _expand_skeleton_ownership,
    _identify_cell_bodies_cellprofiler,
    _physically_soma_rooted_owner_mask,
    _propagate_neurite_owner_regions,
    _repair_signal_supported_skeleton,
    _render_owned_skeleton,
    _seeded_candidate_components,
    _TopologyResult,
    count_neuronal_cell_bodies_metaxpress,
    neurite_outgrowth_metaxpress,
)
from openhcs.processing.materialization import (
    ImageFileOptions,
    ROIOptions,
    SpatialGraphROIOptions,
    SWCOptions,
    materialize,
)


def _implementation():
    return CallableContract.from_callable(
        neurite_outgrowth_metaxpress
    ).resolve_raw_runtime_callable()


def _cell_body_count_implementation():
    return CallableContract.from_callable(
        count_neuronal_cell_bodies_metaxpress
    ).resolve_raw_runtime_callable()


def _rows(rows):
    return rows.row_mappings()


def _draw_fluorescent_neuron(*, crossing=False, branched=False):
    image = np.zeros((1, 128, 128), dtype=np.uint16)
    rows, columns = disk((64, 20), 9, shape=image.shape[1:])
    image[0, rows, columns] = 1000
    rows, columns = line(64, 28, 64, 115)
    image[0, rows, columns] = 700
    if crossing:
        rows, columns = line(20, 75, 110, 75)
        image[0, rows, columns] = 700
    if branched:
        rows, columns = line(64, 75, 35, 105)
        image[0, rows, columns] = 700
        rows, columns = line(64, 75, 93, 105)
        image[0, rows, columns] = 700
    return image


def _cell_body_settings(channel_index=None):
    return MetaXpressCellBodySettings(
        approximate_max_width=30.0,
        minimum_area=100.0,
        intensity_above_local_background=100.0,
        channel_index=channel_index,
    )


def _outgrowth_settings(significant_threshold=20.0):
    return MetaXpressOutgrowthSettings(
        maximum_width=3.0,
        intensity_above_local_background=100.0,
        minimum_cell_growth_to_log_as_significant=significant_threshold,
    )


def _with_separate_body_channel(neurite_stack):
    body_image = np.zeros_like(neurite_stack[0])
    rows, columns = disk((64, 20), 9, shape=body_image.shape)
    body_image[rows, columns] = 1000
    return np.stack((body_image, neurite_stack[0]))


def test_signature_exposes_documented_metaxpress_controls_only():
    parameters = signature(_implementation()).parameters
    contract = CallableContract.from_callable(neurite_outgrowth_metaxpress)
    runtime_artifact_parameter_names = contract.artifact_inputs.names()
    exposed = [
        name for name in parameters if name not in runtime_artifact_parameter_names
    ]

    assert exposed == [
        "image",
        "neurite_channel_index",
        "illumination",
        "cell_body",
        "outgrowth",
        "use_nuclear_stain",
        "nuclear_stain",
    ]
    assert runtime_artifact_parameter_names == ("pixel_size",)
    assert parameters["pixel_size"].annotation._ui_hidden is True
    assert [field.name for field in fields(MetaXpressCellBodySettings)] == [
        "approximate_max_width",
        "minimum_area",
        "intensity_above_local_background",
        "channel_index",
    ]
    assert [field.name for field in fields(MetaXpressOutgrowthSettings)] == [
        "maximum_width",
        "intensity_above_local_background",
        "minimum_cell_growth_to_log_as_significant",
        "candidate_threshold_correction_factor",
        "candidate_hysteresis_seed_correction_factor",
    ]
    assert [field.name for field in fields(MetaXpressNuclearSettings)] == [
        "channel_index",
        "approx_min_width",
        "approx_max_width",
        "intensity_above_local_background",
    ]
    assert [choice.value for choice in NeuriteIllumination] == [
        "fluorescence",
        "transmission",
    ]
    assert contract.artifact_outputs.names() == (
        "neurite_outgrowth_summary",
        "neurite_outgrowth_cells",
        "cell_bodies",
        "neurite_outgrowth",
        "neurons",
        "nuclei",
        "neurite_candidate_mask",
        "neurite_unrooted_residual",
        "neurite_secondary_ownership",
        "neurite_topology_dropped_trace",
        "neurite_topology_added_trace",
        "neurite_morphology",
    )
    (
        summary_spec,
        cell_spec,
        body_spec,
        neurite_spec,
        neurons_spec,
        nuclei_spec,
        candidate_spec,
        residual_spec,
        secondary_ownership_spec,
        topology_dropped_trace_spec,
        topology_added_trace_spec,
        morphology_spec,
    ) = contract.artifact_outputs
    assert summary_spec.artifact_type is MeasurementsArtifactType
    assert cell_spec.artifact_type is MeasurementsArtifactType
    assert cell_spec.relations[0].measurement_subject().name == neurons_spec.name
    assert cell_spec.relations[0].measurement_subject().id_field == "cell"
    assert all(
        spec.artifact_type is ObjectLabelsArtifactType
        for spec in (body_spec, neurite_spec, neurons_spec, nuclei_spec)
    )
    for spec in (body_spec, neurite_spec, neurons_spec, nuclei_spec):
        assert spec.materialization is NEURITE_OBJECT_LABEL_MATERIALIZATION
        assert tuple(type(output) for output in spec.materialization.outputs) == (
            ROIOptions,
            ImageFileOptions,
        )
        assert spec.materialization.primary == 0
    for spec in (
        candidate_spec,
        residual_spec,
        secondary_ownership_spec,
        topology_dropped_trace_spec,
        topology_added_trace_spec,
    ):
        assert spec.artifact_type is ImageArtifactType
        assert spec.sidecar_role is ArtifactSidecarRole.QA_CHECKPOINT
        assert spec.viewer_streaming is ArtifactViewerStreaming.ON_DEMAND
        assert tuple(type(output) for output in spec.materialization.outputs) == (
            ImageFileOptions,
        )
        assert spec.materialization.primary == 0
    assert morphology_spec.artifact_type is SpatialGraphArtifactType
    morphology_subject = morphology_spec.relations[0].object_subject_binding()
    assert morphology_subject.source == neurons_spec.ref()
    assert morphology_subject.id_field == "label"
    assert tuple(
        type(output) for output in morphology_spec.materialization.outputs
    ) == (
        SWCOptions,
        SpatialGraphROIOptions,
    )


def test_neurite_label_materialization_preserves_exact_pixels_below_roi_area_cutoff(
    tmp_path,
):
    labels = np.zeros((16, 24), dtype=np.int32)
    labels[1, 2] = 70001
    labels[5:9, 8:13] = 123
    payload = ObjectLabelPayload(variant_data=ObjectLabelVariantData(labels=labels))
    filemanager = FileManager({"disk": DiskStorageBackend()})
    materialize(
        NEURITE_OBJECT_LABEL_MATERIALIZATION,
        data=payload,
        path=str(tmp_path / "neurons.roi.zip"),
        filemanager=filemanager,
        backends=["disk"],
        backend_kwargs={},
    )
    paths = tuple(tmp_path.glob("*.labels.tif"))
    assert len(paths) == 1
    retained = tifffile.imread(paths[0])
    assert retained.dtype == labels.dtype
    np.testing.assert_array_equal(retained, labels)
    assert tuple(tmp_path.glob("*rois.roi.zip"))


def test_cell_body_minimum_area_does_not_impose_hidden_roundness(monkeypatch):
    image = np.zeros((96, 96), dtype=np.uint16)
    image[42:54, 30:60] = 2000
    detected_labels = np.zeros(image.shape, dtype=np.int32)
    detected_labels[42:54, 30:60] = 1

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth.identify_primary_objects",
        lambda *_args, **_kwargs: (image, image, detected_labels),
    )

    payload = _identify_cell_bodies_cellprofiler(
        image,
        MetaXpressCellBodySettings(
            approximate_max_width=30.0,
            minimum_area=300.0,
            intensity_above_local_background=100.0,
        ),
        1.0,
        bright_objects=True,
    )

    assert np.array_equal(
        object_label_dense_array(payload, dtype=np.int32),
        detected_labels,
    )


def test_nuclear_support_ignores_rejected_nearer_body_candidate(monkeypatch):
    image = np.zeros((96, 96), dtype=np.uint16)
    image[38:60, 28:50] = 2000
    image[47:50, 54:57] = 2000
    detected_labels = np.zeros(image.shape, dtype=np.int32)
    detected_labels[38:60, 28:50] = 1
    detected_labels[47:50, 54:57] = 2
    nuclei_labels = np.zeros(image.shape, dtype=np.int32)
    nuclei_labels[46:51, 53:58] = 1

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth.identify_primary_objects",
        lambda *_args, **_kwargs: (image, image, detected_labels),
    )
    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth.local_background_response",
        lambda *_args, **_kwargs: np.where(image > 0, 1000.0, 0.0),
    )

    payload = _identify_cell_bodies_cellprofiler(
        image,
        MetaXpressCellBodySettings(
            approximate_max_width=30.0,
            minimum_area=100.0,
            intensity_above_local_background=100.0,
        ),
        1.0,
        bright_objects=True,
        nuclei_labels=nuclei_labels,
    )

    expected = np.zeros(image.shape, dtype=np.int32)
    expected[38:60, 28:50] = 1
    assert np.array_equal(
        object_label_dense_array(payload, dtype=np.int32),
        expected,
    )


def test_independent_neuronal_cell_body_counter_has_no_neurite_contract():
    image = np.zeros((2, 128, 128), dtype=np.uint16)
    rows, columns = disk((64, 64), 12, shape=image.shape[1:])
    image[0, rows, columns] = 1200
    rows, columns = disk((64, 64), 6, shape=image.shape[1:])
    image[1, rows, columns] = 1400

    result = _cell_body_count_implementation()(
        image,
        cell_body=MetaXpressCellBodySettings(
            approximate_max_width=30.0,
            minimum_area=100.0,
            intensity_above_local_background=100.0,
            channel_index=0,
        ),
        nuclear_stain=MetaXpressNuclearSettings(
            channel_index=1,
            approx_min_width=6.0,
            approx_max_width=20.0,
            intensity_above_local_background=200.0,
        ),
        pixel_size=1.0,
    )

    summary = _rows(result[1])[0]
    cells = _rows(result[2])
    assert summary["neuronal_cell_body_count"] == 1
    assert summary["nuclei_detected"] == 1
    assert len(cells) == 1
    assert cells[0]["cell"] == 1
    assert result[3][0].max() == 1
    assert result[4][1].max() == 1
    assert CallableContract.from_callable(
        count_neuronal_cell_bodies_metaxpress
    ).artifact_outputs.names() == (
        "neuronal_cell_body_summary",
        "neuronal_cell_body_measurements",
        "neuronal_cell_bodies",
        "nuclei",
    )


def test_independent_counter_propagates_nuclear_seed_through_soma_signal(monkeypatch):
    image = np.zeros((2, 128, 128), dtype=np.uint16)
    image[0, 50:62, 40:46] = 1200
    image[0, 50:62, 47:53] = 1200
    rows, columns = disk((56, 46), 5, shape=image.shape[1:])
    image[1, rows, columns] = 1400
    calls = []

    def propagated_secondary(body_image, *, primary_labels, **kwargs):
        calls.append((body_image, primary_labels, kwargs))
        propagated = np.zeros(body_image.shape, dtype=np.int32)
        propagated[50:62, 40:53] = 1
        return body_image, primary_labels.with_replacement_labels(propagated)

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth.identify_secondary_objects",
        propagated_secondary,
    )
    result = _cell_body_count_implementation()(
        image,
        cell_body=MetaXpressCellBodySettings(
            approximate_max_width=30.0,
            minimum_area=100.0,
            intensity_above_local_background=100.0,
            channel_index=0,
        ),
        nuclear_stain=MetaXpressNuclearSettings(
            channel_index=1,
            approx_min_width=6.0,
            approx_max_width=20.0,
            intensity_above_local_background=200.0,
        ),
        pixel_size=1.0,
    )

    assert len(calls) == 1
    assert int(object_label_dense_array(calls[0][1]).max()) == 1
    assert _rows(result[1])[0]["neuronal_cell_body_count"] == 1
    assert result[3][0, 56, 46] == 1


def test_topology_metrics_and_significant_threshold_is_scoring_only():
    image = _with_separate_body_channel(_draw_fluorescent_neuron(branched=True))
    low_threshold = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(20.0),
        pixel_size=1.0,
    )
    high_threshold = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(1000.0),
        pixel_size=1.0,
    )

    low_summary = _rows(low_threshold[1])[0]
    low_cell = _rows(low_threshold[2])[0]
    high_summary = _rows(high_threshold[1])[0]
    high_cell = _rows(high_threshold[2])[0]

    assert low_summary["number_of_cells"] == 1
    assert low_summary["total_processes"] > 0
    assert low_summary["total_processes"] == high_summary["total_processes"]
    assert low_summary["total_branches"] == high_summary["total_branches"]
    assert low_cell["mean_process_length_um"] == pytest.approx(
        low_cell["total_outgrowth_um"] / low_cell["processes"]
    )
    assert 0.0 < low_cell["straightness"] <= 1.0
    assert low_cell["significant_growth"] is True
    assert high_cell["significant_growth"] is False
    assert high_summary["cells_significant_growth"] == 0
    assert high_cell["total_outgrowth_um"] == pytest.approx(
        low_cell["total_outgrowth_um"]
    )
    assert np.array_equal(
        low_threshold[4],
        high_threshold[4],
    )


def test_unrooted_crossing_arm_is_not_reported_as_a_branch():
    image = _with_separate_body_channel(_draw_fluorescent_neuron(crossing=True))
    (_, summary_rows, cell_rows, _, neurite_labels, _, _, _, *_) = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )

    summary = _rows(summary_rows)[0]
    cell = _rows(cell_rows)[0]
    neurite_mask = neurite_labels[1]
    assert summary["resolved_crossovers"] == 0
    assert summary["total_branches"] == cell["branches"] == 0
    assert summary["total_processes"] == cell["processes"] > 0
    assert 0.0 < cell["straightness"] <= 1.0
    assert cell["total_outgrowth_um"] > 80.0
    assert np.count_nonzero(neurite_mask[:, 75]) == 1
    assert np.count_nonzero(neurite_mask[64, :]) > 80


@pytest.mark.parametrize(
    "coordinates",
    ((), ((16, 16),), ((0, 0), (0, 32), (16, 16), (32, 32))),
)
def test_edgeless_skeleton_has_empty_topology(coordinates):
    skeleton = np.zeros((33, 33), dtype=bool)
    for coordinate in coordinates:
        skeleton[coordinate] = True
    original = skeleton.copy()
    topology = _analyze_topology(
        skeleton, np.zeros(skeleton.shape, np.int32), 1.3556, 3.0
    )
    assert all(len(getattr(topology, field.name)) == 0 for field in fields(topology))
    assert np.array_equal(skeleton, original)


def test_sparse_owned_singleton_regression_has_no_neurite_paths():
    import hashlib

    skeleton = np.zeros((1024, 1024), dtype=bool)
    skeleton[599, 168] = True
    assert (
        hashlib.sha256(skeleton.tobytes()).hexdigest()
        == "20dee1df23f3a7a23408e3d3091477e7cc57aedb726e232a2481fd89f8faa015"
    )
    cell_bodies = np.zeros(skeleton.shape, np.int32)
    cell_bodies[599, 168] = 2
    topology = _analyze_topology(
        skeleton,
        cell_bodies,
        1.3556,
        4.0 / 1.3556,
        assigned_path_labels=cell_bodies,
    )
    assert all(len(getattr(topology, field.name)) == 0 for field in fields(topology))


@pytest.mark.parametrize("diagonal", (False, True))
def test_isolated_pixels_do_not_change_connected_path_geometry_or_ownership(diagonal):
    skeleton = np.zeros((33, 33), dtype=bool)
    if diagonal:
        skeleton[np.arange(8, 25), np.arange(8, 25)] = True
    else:
        skeleton[16, 8:25] = True
    bodies = np.zeros(skeleton.shape, np.int32)
    bodies[6:10, 6:10] = 1
    bodies[14:19, 6:10] = 1
    expected = _analyze_topology(skeleton, bodies, 1.3556, 3.0)
    skeleton[0, 0] = skeleton[0, 32] = skeleton[32, 0] = True
    actual = _analyze_topology(skeleton, bodies, 1.3556, 3.0)
    assert np.array_equal(actual.path_lengths, expected.path_lengths)
    assert np.array_equal(actual.path_owners, expected.path_owners)
    assert np.array_equal(actual.path_distances, expected.path_distances)
    assert actual.path_endpoint_groups == expected.path_endpoint_groups
    assert actual.transitions == expected.transitions
    assert len(actual.path_coordinates) == len(expected.path_coordinates) == 1
    assert all(
        np.array_equal(left, right)
        for left, right in zip(actual.path_coordinates, expected.path_coordinates)
    )


def test_three_pixel_cycle_has_empty_topology():
    skeleton = np.zeros((17, 17), dtype=bool)
    skeleton[7, 7] = skeleton[7, 8] = skeleton[8, 7] = True
    original = skeleton.copy()

    topology = _analyze_topology(
        skeleton,
        np.zeros(skeleton.shape, dtype=np.int32),
        pixel_size_um=1.0,
        outgrowth_width_px=3.0,
    )

    assert all(len(getattr(topology, field.name)) == 0 for field in fields(topology))
    np.testing.assert_array_equal(skeleton, original)


def test_three_pixel_cycle_does_not_change_valid_path_topology():
    skeleton = np.zeros((33, 33), dtype=bool)
    skeleton[16, 8:25] = True
    bodies = np.zeros(skeleton.shape, dtype=np.int32)
    bodies[14:19, 6:10] = 1
    expected = _analyze_topology(skeleton, bodies, 1.0, 3.0)

    skeleton[2, 2] = skeleton[2, 3] = skeleton[3, 2] = True
    actual = _analyze_topology(skeleton, bodies, 1.0, 3.0)

    np.testing.assert_array_equal(actual.path_lengths, expected.path_lengths)
    np.testing.assert_array_equal(actual.path_owners, expected.path_owners)
    np.testing.assert_array_equal(actual.path_distances, expected.path_distances)
    assert actual.path_endpoint_groups == expected.path_endpoint_groups
    assert actual.transitions == expected.transitions
    assert all(
        np.array_equal(left, right)
        for left, right in zip(actual.path_coordinates, expected.path_coordinates)
    )


def test_owned_topology_ignores_three_pixel_cycle_for_separate_owner():
    owned = np.zeros((33, 33), dtype=np.int32)
    owned[16, 8:25] = 1
    owned[2, 2] = owned[2, 3] = owned[3, 2] = 2
    bodies = np.zeros_like(owned)
    bodies[14:19, 6:10] = 1
    bodies[1:5, 1:5] = 2

    topology = _analyze_owned_topology(
        owned,
        bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=3.0,
    )
    rendered = _render_owned_skeleton(owned.shape, topology)

    assert len(topology.path_coordinates) == 1
    assert np.all(topology.path_owners == 1)
    np.testing.assert_array_equal(rendered > 0, owned == 1)


def test_crossing_resolution_retains_two_logical_endpoint_groups():
    skeleton = np.zeros((65, 65), dtype=bool)
    skeleton[32, 5:60] = True
    skeleton[5:60, 32] = True
    cell_bodies = np.zeros(skeleton.shape, dtype=np.int32)
    cell_bodies[30:35, 3:9] = 1

    topology = _analyze_topology(
        skeleton,
        cell_bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=3.0,
    )

    crossing_groups = []
    for coordinates, endpoint_groups in zip(
        topology.path_coordinates,
        topology.path_endpoint_groups,
    ):
        for endpoint_index, coordinate in enumerate((coordinates[0], coordinates[-1])):
            if tuple(coordinate) == (32, 32):
                crossing_groups.append(endpoint_groups[endpoint_index])

    assert len(crossing_groups) == 4
    assert len(set(crossing_groups)) == 2
    assert sorted(crossing_groups.count(group) for group in set(crossing_groups)) == [
        2,
        2,
    ]
    assert np.all(topology.path_branch_types == 0)


def test_owned_geometric_crossing_uses_nominal_owner_as_branch():
    owned = np.zeros((65, 65), dtype=np.int32)
    bodies = np.zeros_like(owned)
    bodies[29:36, 2:9] = 1
    owned[32, 9:57] = 1
    owned[8:57, 32] = 1

    topology = _analyze_owned_topology(
        owned,
        bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=2.0,
    )
    rendered = _render_owned_skeleton(owned.shape, topology)

    np.testing.assert_array_equal(rendered > 0, owned > 0)
    assert np.all(topology.path_owners == 1)
    assert topology.crossing_nodes == frozenset()
    assert len(topology.branch_nodes_by_cell[1]) == 1


@pytest.mark.parametrize("pixel_size_um", [0.5, 1.0, 1.3556, 2.0])
def test_short_two_junction_crossing_resolves_opposite_rooted_traces(pixel_size_um):
    skeleton = np.zeros((70, 70), dtype=bool)
    first_junction = (32, 30)
    second_junction = (35, 34)
    terminals = ((32, 5), (55, 15), (35, 60), (10, 50))
    for start, end in (
        (first_junction, second_junction),
        (first_junction, terminals[0]),
        (first_junction, terminals[1]),
        (second_junction, terminals[2]),
        (second_junction, terminals[3]),
    ):
        rows, columns = line(*start, *end)
        skeleton[rows, columns] = True
    cell_bodies = np.zeros(skeleton.shape, dtype=np.int32)
    cell_bodies[30:35, 3:9] = 1
    cell_bodies[7:13, 47:53] = 2

    topology = _analyze_topology(
        skeleton,
        cell_bodies,
        pixel_size_um=pixel_size_um,
        outgrowth_width_px=8.0,
    )

    assert len(topology.crossing_nodes) == 1
    assert len(topology.crossing_core_paths) == 1
    assert len(topology.crossing_paths) == 4
    assert topology.branch_nodes_by_cell == {}
    assert topology.path_owners[next(iter(topology.crossing_core_paths))] == 0
    terminal_owners = {
        tuple(coordinate): int(topology.path_owners[path_index])
        for path_index, coordinates in enumerate(topology.path_coordinates)
        for coordinate in (coordinates[0], coordinates[-1])
        if tuple(coordinate) in terminals
    }
    assert terminal_owners == {
        (32, 5): 1,
        (55, 15): 2,
        (35, 60): 1,
        (10, 50): 2,
    }
    assert all(
        len(topology.transitions[path_index]) == 1
        for path_index in topology.crossing_paths
    )
    assert all(
        topology.path_branch_types[path_index] == 0
        for path_index in topology.crossing_paths
    )

    morphology = _build_neurite_morphology_graph(
        topology,
        cell_bodies,
        pixel_size_um=pixel_size_um,
        outgrowth_width_px=8.0,
    )
    morphology.require_directed_forest()
    assert len(morphology.edges) == 4
    assert {edge.feature_mapping()["neuron_label"] for edge in morphology.edges} == {
        1,
        2,
    }
    assert {edge.feature_mapping()["branch_type"] for edge in morphology.edges} == {0}


@pytest.mark.parametrize(
    "arm_owners, expected_branch_cells",
    [((1, 2, 3), ()), ((1, 1, 2), ()), ((1, 1, 1), (1,))],
)
@pytest.mark.parametrize("use_assigned_owners", [False, True])
def test_branch_events_require_three_paths_of_the_same_final_owner(
    arm_owners, expected_branch_cells, use_assigned_owners
):
    labels = np.zeros((41, 41), dtype=np.int32)
    labels[20, 7:21] = arm_owners[0]
    labels[20, 21:34] = arm_owners[1]
    labels[21:34, 20] = arm_owners[2]
    bodies = np.zeros(labels.shape, dtype=np.int32)
    for owner, center in zip(arm_owners, ((20, 4), (20, 36), (36, 20))):
        rows, columns = disk(center, radius=3, shape=bodies.shape)
        bodies[rows, columns] = owner

    topology = _analyze_topology(
        labels > 0,
        bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=1.0,
        assigned_path_labels=labels if use_assigned_owners else None,
    )

    assert tuple(sorted(topology.branch_nodes_by_cell)) == expected_branch_cells
    assert all(len(nodes) == 1 for nodes in topology.branch_nodes_by_cell.values())
    assert sorted(topology.path_owners) == sorted(arm_owners)
    morphology = _build_neurite_morphology_graph(
        topology,
        bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=1.0,
    )
    morphology.require_directed_forest()
    assert {edge.feature_mapping()["branch_type"] for edge in morphology.edges} == (
        {1} if expected_branch_cells else {0}
    )


def test_nearby_nonopposite_junctions_remain_a_branch_event():
    skeleton = np.zeros((70, 70), dtype=bool)
    first_junction = (32, 30)
    second_junction = (35, 34)
    for start, end in (
        (first_junction, second_junction),
        (first_junction, (32, 5)),
        (first_junction, (15, 28)),
        (second_junction, (35, 60)),
        (second_junction, (15, 38)),
    ):
        rows, columns = line(*start, *end)
        skeleton[rows, columns] = True
    cell_bodies = np.zeros(skeleton.shape, dtype=np.int32)
    cell_bodies[30:35, 3:9] = 1

    topology = _analyze_topology(
        skeleton,
        cell_bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=8.0,
    )

    assert topology.crossing_nodes == frozenset()
    assert topology.crossing_core_paths == frozenset()
    assert len(topology.branch_nodes_by_cell[1]) == 1


def test_neurite_morphology_is_soma_rooted_feature_bearing_forest():
    image = _with_separate_body_channel(_draw_fluorescent_neuron(branched=True))

    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )
    cell_bodies = result[3][0]
    neurite_labels = result[4][1]
    morphology = result[-1]

    assert isinstance(morphology, SpatialGraph)
    morphology.require_directed_forest()
    assert morphology.name == "neurite_morphology"
    assert morphology.coordinate_spacing == (1.0, 1.0)
    assert len(morphology.roots()) == 1
    assert len(morphology.edges) == len(morphology.nodes) - len(morphology.roots())
    assert morphology.roots()[0].feature_mapping() == {
        "label": 1,
        "neuron_label": 1,
        "node_role": "soma_attachment_root",
    }
    root_index = tuple(int(value) for value in morphology.roots()[0].coordinates)
    assert cell_bodies[root_index] == 0
    assert ndi.binary_dilation(cell_bodies == 1)[root_index]
    assert not np.any((neurite_labels > 0) & (cell_bodies > 0))
    expected_edge_features = {
        "label",
        "neuron_label",
        "branch_distance_um",
        "euclidean_distance_um",
        "tortuosity",
        "distance_from_soma_um",
        "branch_type",
    }
    for edge in morphology.edges:
        features = edge.feature_mapping()
        assert set(features) == expected_edge_features
        assert features["label"] == features["neuron_label"] == 1
        assert features["branch_distance_um"] > 0
        assert features["euclidean_distance_um"] > 0
        assert features["tortuosity"] >= 1.0
        assert features["distance_from_soma_um"] >= 0
        coordinates = np.rint(edge.coordinates).astype(int)
        assert not np.any(cell_bodies[tuple(coordinates.T)] > 0)


@pytest.mark.parametrize("branched", [False, True])
@pytest.mark.parametrize("pixel_size", [0.5, 1.0, 1.3556])
def test_cell_lengths_measure_the_published_owned_paths(branched, pixel_size):
    image = _with_separate_body_channel(_draw_fluorescent_neuron(branched=branched))
    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=MetaXpressCellBodySettings(
            approximate_max_width=30.0 * pixel_size,
            minimum_area=100.0 * pixel_size**2,
            intensity_above_local_background=100.0,
            channel_index=0,
        ),
        outgrowth=MetaXpressOutgrowthSettings(
            maximum_width=3.0 * pixel_size,
            intensity_above_local_background=100.0,
            minimum_cell_growth_to_log_as_significant=20.0,
        ),
        pixel_size=pixel_size,
    )
    morphology = result[-1]
    cells = _rows(result[2])
    assert cells
    for cell in cells:
        owned_lengths = [
            edge.feature_mapping()["branch_distance_um"]
            for edge in morphology.edges
            if edge.feature_mapping()["neuron_label"] == cell["cell"]
        ]
        assert owned_lengths
        assert cell["total_outgrowth_um"] == pytest.approx(sum(owned_lengths))
        assert cell["mean_process_length_um"] == pytest.approx(
            cell["total_outgrowth_um"] / cell["processes"]
        )
        assert 0 <= cell["median_process_length_um"] <= cell["max_process_length_um"]
        assert cell["max_process_length_um"] <= cell["total_outgrowth_um"]
        # At least ceil(N / 2) nonnegative values are at least their median.
        assert cell["median_process_length_um"] * ((cell["processes"] + 1) // 2) <= (
            cell["total_outgrowth_um"] + 1e-8
        )


def test_neurite_morphology_provenance_selects_the_neurite_plane():
    image = _with_separate_body_channel(_draw_fluorescent_neuron(branched=True))

    morphology = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )[-1]

    assert morphology.source_plane_index == 1


def test_neurite_morphology_breaks_cycle_without_dropping_path_geometry():
    path_coordinates = (
        np.array([[8, 8], [8, 20]], dtype=int),
        np.array([[8, 20], [20, 20]], dtype=int),
        np.array([[20, 20], [8, 8]], dtype=int),
    )
    topology = _TopologyResult(
        path_owners=np.ones(3, dtype=np.int32),
        path_distances=np.array([0.0, 12.0, 12.0]),
        path_lengths=np.array([12.0, 12.0, np.hypot(12.0, 12.0)]),
        path_euclidean_lengths=np.array([12.0, 12.0, np.hypot(12.0, 12.0)]),
        path_coordinates=path_coordinates,
        path_endpoint_groups=((1, 2), (2, 3), (3, 1)),
        path_branch_types=np.full(3, 2, dtype=np.int32),
        endpoint_group_coordinates={
            1: (8.0, 8.0),
            2: (8.0, 20.0),
            3: (20.0, 20.0),
        },
        transitions={0: (1, 2), 1: (0, 2), 2: (0, 1)},
        root_paths_by_cell={1: (0, 2)},
        branch_nodes_by_cell={},
        crossing_nodes=frozenset(),
        crossing_paths=frozenset(),
        crossing_core_paths=frozenset(),
    )
    cell_bodies = np.zeros((32, 32), dtype=np.int32)
    cell_bodies[6:11, 6:11] = 1

    morphology = _build_neurite_morphology_graph(
        topology,
        cell_bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=3.0,
    )

    morphology.require_directed_forest()
    assert len(morphology.nodes) == 4
    assert len(morphology.edges) == 3
    assert len(morphology.roots()) == 1
    assert (
        sum(
            node.feature_mapping().get("node_role") == "cycle_break"
            for node in morphology.nodes
        )
        == 1
    )
    assert {
        tuple(int(value) for value in coordinate)
        for edge in morphology.edges
        for coordinate in edge.coordinates
    } >= {
        tuple(int(value) for value in coordinate)
        for path in path_coordinates
        for coordinate in path
    }


def test_neurite_morphology_does_not_fabricate_links_between_components():
    topology = _TopologyResult(
        path_owners=np.ones(2, dtype=np.int32),
        path_distances=np.zeros(2, dtype=float),
        path_lengths=np.array([8.0, 10.0]),
        path_euclidean_lengths=np.array([8.0, 10.0]),
        path_coordinates=(
            np.array([[12, 12], [12, 20]], dtype=int),
            np.array([[14, 12], [24, 12]], dtype=int),
        ),
        path_endpoint_groups=((1, 2), (3, 4)),
        path_branch_types=np.zeros(2, dtype=np.int32),
        endpoint_group_coordinates={
            1: (12.0, 12.0),
            2: (12.0, 20.0),
            3: (14.0, 12.0),
            4: (24.0, 12.0),
        },
        transitions={0: (), 1: ()},
        root_paths_by_cell={1: (0, 1)},
        branch_nodes_by_cell={},
        crossing_nodes=frozenset(),
        crossing_paths=frozenset(),
        crossing_core_paths=frozenset(),
    )
    cell_bodies = np.zeros((32, 32), dtype=np.int32)
    cell_bodies[10:17, 9:14] = 1

    morphology = _build_neurite_morphology_graph(
        topology,
        cell_bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=3.0,
    )

    assert len(morphology.roots()) == 2
    assert len(morphology.edges) == 2
    assert {edge.source.node_id for edge in morphology.edges} == {
        root.node_id for root in morphology.roots()
    }
    for edge in morphology.edges:
        segment_lengths = np.linalg.norm(np.diff(edge.coordinates, axis=0), axis=1)
        assert edge.feature_mapping()["branch_distance_um"] == pytest.approx(
            float(segment_lengths.sum())
        )
        assert tuple(edge.coordinates[0]) in {(12.0, 12.0), (14.0, 12.0)}


def test_disconnected_neurites_are_absent_from_owned_output_and_measurements():
    baseline_image = _with_separate_body_channel(_draw_fluorescent_neuron())
    image = baseline_image.copy()
    rows, columns = line(20, 50, 20, 110)
    image[1, rows, columns] = 700

    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )
    baseline = _implementation()(
        baseline_image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )

    assert not result[4][1, 20, 80]
    assert result[4][1, 64, 80]
    assert _rows(result[1])[0]["total_outgrowth_um"] == pytest.approx(
        _rows(baseline[1])[0]["total_outgrowth_um"]
    )


def test_explicit_body_nuclear_and_neurite_channels_are_aligned():
    neurite_image = _draw_fluorescent_neuron()[0]
    body_image = np.zeros_like(neurite_image)
    rows, columns = disk((64, 20), 9, shape=body_image.shape)
    body_image[rows, columns] = 1000
    nucleus_image = np.zeros_like(neurite_image)
    rows, columns = disk((64, 20), 5, shape=nucleus_image.shape)
    nucleus_image[rows, columns] = 1200
    image = np.stack((nucleus_image, body_image, neurite_image))

    (
        _,
        summary_rows,
        cell_rows,
        cell_bodies,
        neurite_labels,
        neurons,
        nuclei,
        candidate_mask,
        unrooted_residual,
        secondary_ownership,
        topology_dropped_trace,
        topology_added_trace,
        morphology,
    ) = _implementation()(
        image,
        neurite_channel_index=2,
        cell_body=_cell_body_settings(channel_index=1),
        outgrowth=_outgrowth_settings(),
        use_nuclear_stain=True,
        nuclear_stain=MetaXpressNuclearSettings(
            channel_index=0,
            approx_min_width=6.0,
            approx_max_width=14.0,
            intensity_above_local_background=200.0,
        ),
        pixel_size=1.0,
    )

    summary = _rows(summary_rows)[0]
    assert summary["number_of_cells"] == 1
    assert summary["neurite_channel_index"] == 2
    assert summary["cell_body_channel_index"] == 1
    assert summary["nuclear_channel_index"] == 0
    assert {row["slice_index"] for row in _rows(cell_rows)} == {1}
    assert cell_bodies.shape == neurite_labels.shape == nuclei.shape == image.shape
    assert cell_bodies[1].max() == 1
    assert np.count_nonzero(cell_bodies[[0, 2]]) == 0
    assert neurite_labels[2].max() == 1
    assert np.count_nonzero(neurite_labels[[0, 1]]) == 0
    assert neurons[2].max() == 1
    assert neurons[2, 64, 20] == 1
    assert neurons[2, 64, 80] == 1
    assert np.count_nonzero(neurons[[0, 1]]) == 0
    assert nuclei[0].max() == 1
    assert np.count_nonzero(nuclei[[1, 2]]) == 0
    assert isinstance(morphology, SpatialGraph)
    assert candidate_mask.source_indices == (2,)
    assert unrooted_residual.source_indices == (2,)
    assert secondary_ownership.source_indices == (2,)
    assert topology_dropped_trace.source_indices == (2,)
    assert topology_added_trace.source_indices == (2,)
    assert np.asarray(candidate_mask).shape == (1, *image.shape[1:])
    assert np.asarray(unrooted_residual).shape == (1, *image.shape[1:])
    assert np.asarray(secondary_ownership).shape == (1, *image.shape[1:])
    assert np.asarray(topology_dropped_trace).shape == (1, *image.shape[1:])
    assert np.asarray(topology_added_trace).shape == (1, *image.shape[1:])
    assert not np.any(
        np.asarray(topology_dropped_trace)[0] & (cell_bodies[1] > 0)
    )
    assert np.all(np.asarray(unrooted_residual) <= np.asarray(candidate_mask))
    assert not np.any(np.asarray(unrooted_residual)[0] & (cell_bodies[1] > 0))
    candidate_neurite = np.asarray(candidate_mask)[0].astype(bool) & (
        cell_bodies[1] == 0
    )
    residual = np.asarray(unrooted_residual)[0].astype(bool)
    secondary_owned_residual = residual & (
        np.asarray(secondary_ownership)[0] > 0
    )
    assert summary["candidate_mask_pixels"] == np.count_nonzero(candidate_neurite)
    assert summary["rooted_candidate_mask_pixels"] == np.count_nonzero(
        candidate_neurite & (neurons[2] > 0)
    )
    assert summary["unrooted_residual_pixels"] == np.count_nonzero(residual)
    assert summary["secondary_owned_residual_pixels"] == np.count_nonzero(
        secondary_owned_residual
    )
    assert summary["secondary_unowned_residual_pixels"] == np.count_nonzero(
        residual & ~secondary_owned_residual
    )
    assert summary["secondary_owned_residual_fraction"] == pytest.approx(
        np.count_nonzero(secondary_owned_residual) / np.count_nonzero(residual)
        if np.any(residual)
        else 0.0
    )
    assert (
        summary["rooted_candidate_trace_pixels"]
        + summary["unrooted_candidate_trace_pixels"]
        == summary["candidate_trace_pixels"]
    )
    assert summary["rooted_candidate_trace_yield"] == pytest.approx(
        summary["rooted_candidate_trace_pixels"]
        / summary["candidate_trace_pixels"]
        if summary["candidate_trace_pixels"]
        else 0.0
    )
    assert (
        summary["secondary_owned_unrooted_trace_pixels"]
        + summary["secondary_unowned_unrooted_trace_pixels"]
        == summary["unrooted_candidate_trace_pixels"]
    )
    assert summary["initial_topology_owned_trace_pixels"] <= summary[
        "secondary_adopted_trace_pixels"
    ]
    assert summary["published_owned_trace_pixels"] == np.count_nonzero(
        neurite_labels[2]
    )
    assert summary["published_owned_trace_pixels"] >= summary[
        "final_topology_owned_trace_pixels"
    ]
    assert summary["final_topology_dropped_trace_pixels"] == np.count_nonzero(
        np.asarray(topology_dropped_trace)
    )
    assert summary[
        "final_topology_dropped_crossing_support_trace_pixels"
    ] <= summary["final_topology_dropped_trace_pixels"]
    assert (
        summary["final_topology_dropped_unrooted_path_trace_pixels"]
        + summary["final_topology_dropped_unrepresented_trace_pixels"]
        == summary["final_topology_dropped_trace_pixels"]
    )
    assert (
        summary["final_topology_dropped_physically_rooted_path_trace_pixels"]
        + summary["final_topology_dropped_physically_unrooted_path_trace_pixels"]
        == summary["final_topology_dropped_unrooted_path_trace_pixels"]
    )
    assert summary["final_topology_added_trace_pixels"] == np.count_nonzero(
        np.asarray(topology_added_trace)
    )
    assert summary["final_topology_added_trace_pixels"] <= summary[
        "crossing_core_trace_pixels"
    ]


def test_expanded_ownership_preserves_response_repaired_trace_support():
    final_trace = np.zeros((11, 11), dtype=np.int32)
    final_trace[5, 2:9] = 1
    earlier_detector_foreground = final_trace > 0
    earlier_detector_foreground[5, 4:7] = False

    expanded = _expand_skeleton_ownership(
        final_trace, earlier_detector_foreground, outgrowth_width_px=6.0
    )

    np.testing.assert_array_equal(
        expanded[final_trace > 0], final_trace[final_trace > 0]
    )
    assert not np.any(expanded[~(earlier_detector_foreground | (final_trace > 0))])


def test_filled_two_neuron_crossing_keeps_the_same_owners_as_final_traces():
    image = np.zeros((2, 128, 128), dtype=np.uint16)
    for center in ((64, 20), (20, 75)):
        rr, cc = disk(center, 9, shape=image.shape[1:])
        image[:, rr, cc] = 1000
    for start, end in (((64, 28), (64, 115)), ((28, 75), (115, 75))):
        rr, cc = line(*start, *end)
        image[1, rr, cc] = 700

    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )
    summary = _rows(result[1])[0]
    bodies, traces, neurons = result[3][0], result[4][1], result[5][1]
    horizontal_owner = bodies[64, 20]
    vertical_owner = bodies[20, 75]

    assert horizontal_owner > 0 and vertical_owner > 0
    assert horizontal_owner != vertical_owner
    assert summary["resolved_crossovers"] == 1
    assert traces[64, 105] == horizontal_owner
    assert traces[105, 75] == vertical_owner
    assert traces[64, 75] in {horizontal_owner, vertical_owner}
    np.testing.assert_array_equal(neurons[traces > 0], traces[traces > 0])
    np.testing.assert_array_equal(neurons[bodies > 0], bodies[bodies > 0])


def test_final_neurons_project_rooted_trace_ownership(monkeypatch):
    image = _with_separate_body_channel(_draw_fluorescent_neuron(branched=True))

    def broad_secondary_ownership(source_image, primary_labels, **_kwargs):
        del primary_labels
        return np.ones(source_image.shape, dtype=np.int32)

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth."
        "_identify_secondary_owner_regions_cellprofiler",
        broad_secondary_ownership,
    )

    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )

    bodies = result[3][0]
    traces = result[4][1]
    neurons = result[5][1]
    np.testing.assert_array_equal(neurons[bodies > 0], bodies[bodies > 0])
    np.testing.assert_array_equal(neurons[traces > 0], traces[traces > 0])
    assert np.count_nonzero(neurons) > np.count_nonzero(traces)
    expected_owners = set(np.unique(bodies)) | set(np.unique(traces))
    assert set(np.unique(neurons)) == expected_owners
    # Deliberately broad secondary propagation is detection evidence only. The
    # published neuron labels remain bounded to soma-rooted trace ownership.
    assert np.count_nonzero(neurons) < neurons.size


def test_neurite_candidate_and_secondary_ownership_thresholds_are_independent():
    engine = CELLPROFILER_NEURITE_ENGINE_PROFILE
    permissive_candidate_factor = 0.05

    assert (
        engine.threshold_kwargs(
            correction_factor=permissive_candidate_factor,
        )["threshold_correction_factor"]
        == permissive_candidate_factor
    )
    assert (
        engine.secondary_kwargs()["threshold_correction_factor"]
        == engine.secondary_ownership_threshold_correction_factor
    )
    assert permissive_candidate_factor < (
        engine.secondary_ownership_threshold_correction_factor
    )


@pytest.mark.parametrize("correction_factor", [0.0, -0.1, np.inf, np.nan])
def test_outgrowth_settings_reject_invalid_candidate_threshold_correction_factor(
    correction_factor,
):
    settings = MetaXpressOutgrowthSettings(
        candidate_threshold_correction_factor=correction_factor,
    )

    with pytest.raises(
        ValueError,
        match="candidate_threshold_correction_factor must be > 0",
    ):
        settings.validate()


@pytest.mark.parametrize("seed_factor", [0.0, -0.1, np.inf, np.nan])
def test_outgrowth_settings_reject_invalid_hysteresis_seed_factor(seed_factor):
    settings = MetaXpressOutgrowthSettings(
        candidate_hysteresis_seed_correction_factor=seed_factor,
    )

    with pytest.raises(
        ValueError,
        match="candidate_hysteresis_seed_correction_factor must be > 0",
    ):
        settings.validate()


def test_outgrowth_settings_reject_seed_more_permissive_than_candidates():
    settings = MetaXpressOutgrowthSettings(
        candidate_threshold_correction_factor=0.25,
        candidate_hysteresis_seed_correction_factor=0.20,
    )

    with pytest.raises(
        ValueError,
        match="seed_correction_factor must be >=",
    ):
        settings.validate()


def test_seeded_candidate_components_keep_only_components_with_strict_seeds():
    candidates = np.zeros((24, 32), dtype=bool)
    candidates[4, 3:14] = True
    candidates[12, 3:14] = True
    candidates[20, 3:14] = True
    seeds = np.zeros(candidates.shape, dtype=bool)
    seeds[4, 8] = True
    seeds[20, 8] = True
    seeds[0, 0] = True

    retained = _seeded_candidate_components(candidates, seeds)

    assert np.all(retained[4, 3:14])
    assert not np.any(retained[12, 3:14])
    assert np.all(retained[20, 3:14])
    assert not retained[0, 0]


def test_overwide_nuclear_guided_foreground_is_not_a_cell_body():
    image = np.zeros((2, 128, 128), dtype=np.uint16)
    rows, columns = disk((64, 20), 9, shape=image.shape[1:])
    image[0, rows, columns] = 1000
    rows, columns = line(64, 28, 64, 115)
    image[0, rows, columns] = 700
    image[0, 20:65, 70:115] = 1000

    rows, columns = disk((64, 20), 5, shape=image.shape[1:])
    image[1, rows, columns] = 1200
    rows, columns = disk((42, 92), 5, shape=image.shape[1:])
    image[1, rows, columns] = 1200

    _, summary_rows, _, cell_bodies, _, _, nuclei, *_ = _implementation()(
        image,
        cell_body=_cell_body_settings(),
        outgrowth=_outgrowth_settings(),
        use_nuclear_stain=True,
        nuclear_stain=MetaXpressNuclearSettings(
            channel_index=1,
            approx_min_width=6.0,
            approx_max_width=14.0,
            intensity_above_local_background=200.0,
        ),
        pixel_size=1.0,
    )

    assert nuclei[1].max() == 2
    assert _rows(summary_rows)[0]["number_of_cells"] == 1
    assert cell_bodies[0].max() == 1
    assert cell_bodies[0, 64, 20] == 1
    assert cell_bodies[0, 42, 92] == 0


def test_transmission_mode_detects_dark_cell_and_neurite():
    fluorescence = _draw_fluorescent_neuron()[0]
    transmission = np.full(fluorescence.shape, 2000, dtype=np.uint16)
    transmission[fluorescence > 0] = 500

    _, summary_rows, cell_rows, _, _, _, _, *_ = _implementation()(
        transmission[None, ...],
        illumination=NeuriteIllumination.TRANSMISSION,
        cell_body=_cell_body_settings(),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )

    assert _rows(summary_rows)[0]["number_of_cells"] == 1
    assert _rows(summary_rows)[0]["total_processes"] > 0
    assert _rows(cell_rows)[0]["total_outgrowth_um"] > 60.0


def test_cell_rows_do_not_remeasure_owned_paths_with_cp_seed_propagation(monkeypatch):
    image = _with_separate_body_channel(_draw_fluorescent_neuron())

    def forbidden_remeasurement(*args, **kwargs):
        raise AssertionError(
            "Final owned topology must not be reassigned by seed propagation"
        )

    monkeypatch.setattr(
        "openhcs.processing.backends.cellprofiler.skeleton.measure_object_skeleton",
        forbidden_remeasurement,
    )
    _, summary_rows, cell_rows, _, _, _, _, *_ = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=MetaXpressCellBodySettings(
            approximate_max_width=40.0,
            minimum_area=40.0,
            intensity_above_local_background=100.0,
            channel_index=0,
        ),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )

    summary = _rows(summary_rows)[0]
    cell = _rows(cell_rows)[0]
    assert cell["total_outgrowth_um"] > 60.0
    assert cell["processes"] == 1
    assert cell["mean_process_length_um"] == cell["median_process_length_um"]
    assert cell["median_process_length_um"] == cell["max_process_length_um"]
    assert cell["max_process_length_um"] == cell["total_outgrowth_um"]
    assert cell["branches"] == 0
    assert summary["total_outgrowth_um"] == cell["total_outgrowth_um"]
    assert summary["total_processes"] == cell["processes"]
    assert summary["total_branches"] == cell["branches"]


def test_explicit_same_body_channel_remains_valid_and_bounds_are_checked():
    image = _draw_fluorescent_neuron()
    result = _implementation()(
        image,
        neurite_channel_index=0,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        pixel_size=1.0,
    )

    assert _rows(result[1])[0]["cell_body_channel_index"] == 0
    with pytest.raises(ValueError, match="cell_body.channel_index"):
        _implementation()(
            image,
            cell_body=_cell_body_settings(channel_index=1),
            pixel_size=1.0,
        )


def test_body_and_nuclear_channel_may_be_shared():
    neurite_image = _draw_fluorescent_neuron()[0]
    body_and_nucleus = np.zeros_like(neurite_image)
    rows, columns = disk((64, 20), 9, shape=body_and_nucleus.shape)
    body_and_nucleus[rows, columns] = 1200
    image = np.stack((body_and_nucleus, neurite_image))

    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        use_nuclear_stain=True,
        nuclear_stain=MetaXpressNuclearSettings(
            channel_index=0,
            approx_min_width=6.0,
            approx_max_width=20.0,
            intensity_above_local_background=200.0,
        ),
        pixel_size=1.0,
    )

    assert _rows(result[1])[0]["number_of_cells"] == 1
    assert result[3][0].max() == 1
    assert result[6][0].max() == 1


def test_nuclear_body_mode_rejects_non_neuronal_dapi_seed_and_unowned_signal():
    image = np.zeros((2, 160, 160), dtype=np.uint16)
    for center in ((80, 25), (35, 105)):
        rows, columns = disk(center, 9, shape=image.shape[1:])
        image[0, rows, columns] = 1200

    rows, columns = disk((80, 25), 9, shape=image.shape[1:])
    image[1, rows, columns] = 1200
    rows, columns = line(80, 33, 80, 130)
    image[1, rows, columns] = 700
    rows, columns = line(35, 123, 35, 150)
    image[1, rows, columns] = 900

    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=0),
        outgrowth=_outgrowth_settings(),
        use_nuclear_stain=True,
        nuclear_stain=MetaXpressNuclearSettings(
            channel_index=0,
            approx_min_width=6.0,
            approx_max_width=20.0,
            intensity_above_local_background=200.0,
        ),
        pixel_size=1.0,
    )

    summary = _rows(result[1])[0]
    assert summary["number_of_cells"] == 1
    assert result[3][0, 80, 25] == 1
    assert result[3][0, 35, 105] == 0
    assert result[5][1, 80, 100] == 1
    assert {row["cell"] for row in _rows(result[2])} == {1}
    for row in _rows(result[2]):
        assert np.any(result[4][1] == row["cell"])
        assert row["total_outgrowth_um"] > 0
    graph_pixels = np.zeros(image.shape[1:], dtype=bool)
    for edge in result[-1].edges:
        coordinates = np.rint(edge.coordinates).astype(int)
        for start, end in zip(coordinates[:-1], coordinates[1:]):
            rows, columns = line(start[0], start[1], end[0], end[1])
            graph_pixels[rows, columns] = True
    assert np.all(
        ~result[4][1].astype(bool)
        | ndi.binary_dilation(graph_pixels, structure=np.ones((3, 3), dtype=bool))
    )


def test_nuclear_seeds_fill_bounded_signal_bodies_and_keep_zero_growth_cell(
    monkeypatch,
):
    image = np.zeros((2, 160, 160), dtype=np.uint16)
    for center in ((80, 25), (35, 105)):
        rows, columns = disk(center, 5, shape=image.shape[1:])
        image[0, rows, columns] = 1200
        rows, columns = disk(center, 9, shape=image.shape[1:])
        image[1, rows, columns] = 1200
    rows, columns = line(80, 33, 80, 130)
    image[1, rows, columns] = 700

    def reject_discarded_body_segmentation(*args, **kwargs):
        raise AssertionError("nuclear-seeded mode must build directly from its seeds")

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth."
        "_identify_cell_bodies_cellprofiler",
        reject_discarded_body_segmentation,
    )

    def reject_hidden_secondary_threshold(*args, **kwargs):
        raise AssertionError(
            "nuclear-seeded soma admission must use the declared body contract"
        )

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth."
        "_identify_secondary_owner_regions_cellprofiler",
        reject_hidden_secondary_threshold,
    )

    result = _implementation()(
        image,
        neurite_channel_index=1,
        cell_body=_cell_body_settings(channel_index=1),
        outgrowth=_outgrowth_settings(),
        use_nuclear_stain=True,
        nuclear_stain=MetaXpressNuclearSettings(
            channel_index=0,
            approx_min_width=6.0,
            approx_max_width=14.0,
            intensity_above_local_background=200.0,
        ),
        pixel_size=1.0,
    )

    summary = _rows(result[1])[0]
    cell_rows = _rows(result[2])
    cell_bodies = result[3]
    neurites = result[4]
    nuclei = result[6]
    assert summary["number_of_cells"] == 2
    assert np.count_nonzero(cell_bodies[0]) == 0
    assert cell_bodies[1].max() == 2
    assert nuclei[0].max() == 2
    assert np.count_nonzero(nuclei[1]) == 0
    # The centroid-bounded soma leaves a final owned path 89 pixels long.
    # Independent CP seed-relative remeasurement previously reported 42 for
    # this same published path.
    assert sorted(row["total_outgrowth_um"] for row in cell_rows) == [0.0, 89.0]
    zero_growth_cell = next(
        row["cell"] for row in cell_rows if row["total_outgrowth_um"] == 0.0
    )
    assert not np.any(neurites[1] == zero_growth_cell)
    assert zero_growth_cell not in {
        edge.feature_mapping()["neuron_label"] for edge in result[-1].edges
    }
    assert not np.any((cell_bodies[1] > 0) & (neurites[1] > 0))
    assert result[5][1, 35, 140] == 0


def test_neurite_owner_regions_propagate_only_through_declared_signal_support():
    response = np.zeros((32, 32), dtype=float)
    response[16, 3:29] = 150.0
    response[4:17, 3] = 150.0
    bodies = np.zeros(response.shape, dtype=np.int32)
    bodies[4, 3] = 1
    bodies[16, 28] = 2

    owner_regions = _propagate_neurite_owner_regions(
        response,
        bodies,
        minimum_response=100.0,
    )

    assert owner_regions[4, 3] == 1
    assert owner_regions[16, 28] == 2
    assert np.all(owner_regions[4:17, 3] == 1)
    assert np.all(owner_regions[response < 100.0] == 0)
    assert set(np.unique(owner_regions)) == {0, 1, 2}


def test_signal_body_derivation_bounds_each_seed_distance_transform(monkeypatch):
    shape = (512, 512)
    seeds = np.zeros(shape, dtype=np.int32)
    image = np.zeros(shape, dtype=np.uint16)
    for owner, center in (
        (1, (80, 80)),
        (2, (430, 430)),
    ):
        rows, columns = disk(center, 4, shape=shape)
        seeds[rows, columns] = owner
        rows, columns = disk(center, 12, shape=shape)
        image[rows, columns] = 1200

    observed_shapes = []
    distance_transform = ndi.distance_transform_edt

    def record_distance_transform(array, *args, **kwargs):
        observed_shapes.append(array.shape)
        return distance_transform(array, *args, **kwargs)

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth."
        "ndi.distance_transform_edt",
        record_distance_transform,
    )

    bodies = _derive_signal_cell_bodies(
        seeds,
        image,
        _cell_body_settings(channel_index=1),
        1.0,
        bright_objects=True,
    )

    assert set(np.unique(bodies)) == {0, 1, 2}
    assert observed_shapes[0] == shape
    assert len(observed_shapes) == 3
    assert all(
        rows < shape[0] and columns < shape[1] for rows, columns in observed_shapes[1:]
    )


def test_signal_body_derivation_partitions_shared_signal_by_nearest_nucleus():
    shape = (72, 72)
    seeds = np.zeros(shape, dtype=np.int32)
    for owner, center in ((1, (36, 25)), (2, (36, 47))):
        rows, columns = disk(center, 4, shape=shape)
        seeds[rows, columns] = owner
    image = np.zeros(shape, dtype=np.uint16)
    rows, columns = disk((36, 36), 20, shape=shape)
    image[rows, columns] = 1200

    bodies = _derive_signal_cell_bodies(
        seeds,
        image,
        _cell_body_settings(channel_index=1),
        1.0,
        bright_objects=True,
    )

    assert set(np.unique(bodies)) == {0, 1, 2}
    assert bodies[36, 28] == 1
    assert bodies[36, 44] == 2
    assert np.count_nonzero(bodies == 1) > 100
    assert np.count_nonzero(bodies == 2) > 100


def test_signal_body_derivation_enforces_maximum_width_from_nuclear_centroid():
    shape = (96, 96)
    seeds = np.zeros(shape, dtype=np.int32)
    seeds[44:52, 20:76] = 1
    image = np.zeros(shape, dtype=np.uint16)
    image[43:53, 10:86] = 1200

    bodies = _derive_signal_cell_bodies(
        seeds,
        image,
        MetaXpressCellBodySettings(
            approximate_max_width=20.0,
            minimum_area=10.0,
            intensity_above_local_background=100.0,
            channel_index=1,
        ),
        1.0,
        bright_objects=True,
    )

    coordinates = np.argwhere(bodies == 1)
    assert np.ptp(coordinates[:, 0]) <= 20
    assert np.ptp(coordinates[:, 1]) <= 20


def test_signal_body_derivation_rejects_nearby_signal_without_nuclear_overlap(
    monkeypatch,
):
    shape = (64, 64)
    seeds = np.zeros(shape, dtype=np.int32)
    rows, columns = disk((32, 32), 4, shape=shape)
    seeds[rows, columns] = 1
    response = np.zeros(shape, dtype=float)
    rows, columns = disk((32, 43), 4, shape=shape)
    response[rows, columns] = 200.0
    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth."
        "local_background_response",
        lambda *args, **kwargs: response,
    )

    bodies = _derive_signal_cell_bodies(
        seeds,
        response,
        MetaXpressCellBodySettings(
            approximate_max_width=30.0,
            minimum_area=10.0,
            intensity_above_local_background=100.0,
            channel_index=1,
        ),
        1.0,
        bright_objects=True,
    )

    assert not np.any(bodies)


def test_signal_body_derivation_reapplies_minimum_area_after_shared_pixel_overwrite():
    shape = (72, 72)
    seeds = np.zeros(shape, dtype=np.int32)
    for owner, center in ((1, (36, 25)), (2, (36, 47))):
        rows, columns = disk(center, 4, shape=shape)
        seeds[rows, columns] = owner
    image = np.zeros(shape, dtype=np.uint16)
    rows, columns = disk((36, 36), 20, shape=shape)
    image[rows, columns] = 1200

    bodies = _derive_signal_cell_bodies(
        seeds,
        image,
        MetaXpressCellBodySettings(
            approximate_max_width=30.0,
            minimum_area=500.0,
            intensity_above_local_background=100.0,
            channel_index=1,
        ),
        1.0,
        bright_objects=True,
    )

    body_areas = np.bincount(bodies.ravel(), minlength=3)
    assert body_areas[1] == 0
    assert body_areas[2] >= 500


def test_cell_body_contract_bounds_each_object_distance_transform(monkeypatch):
    shape = (512, 512)
    labels = np.zeros(shape, dtype=np.int32)
    response = np.full(shape, 150.0)
    labels[0:11, 0:11] = 1
    labels[245:256, 245:256] = 2

    observed_shapes = []
    distance_transform = ndi.distance_transform_edt

    def record_distance_transform(array, *args, **kwargs):
        observed_shapes.append(array.shape)
        return distance_transform(array, *args, **kwargs)

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth."
        "ndi.distance_transform_edt",
        record_distance_transform,
    )

    keep = _cell_body_contract_candidates(
        labels,
        response,
        minimum_area_px=100.0,
        maximum_width_px=20.0,
        intensity_threshold=100.0,
    )

    np.testing.assert_array_equal(keep, np.array([False, True, True]))
    assert len(observed_shapes) == 2
    assert all(
        rows < shape[0] and columns < shape[1] for rows, columns in observed_shapes
    )


def test_signal_supported_repair_follows_curved_trace_instead_of_chord():
    labels = np.zeros((64, 64), dtype=np.int32)
    labels[32, 8:15] = 1
    labels[32, 45:52] = 1
    cell_bodies = np.zeros_like(labels)
    cell_bodies[29:36, 5:12] = 1
    response = np.zeros(labels.shape, dtype=float)
    first_rows, first_columns = line(32, 14, 18, 28)
    second_rows, second_columns = line(18, 28, 32, 45)
    response[first_rows, first_columns] = 150.0
    response[second_rows, second_columns] = 150.0
    response[labels == 1] = 150.0
    owner_regions = np.zeros_like(labels)
    owner_regions[(response >= 100.0) | (cell_bodies == 1)] = 1

    repaired = _repair_signal_supported_skeleton(
        labels,
        response,
        owner_regions,
        cell_bodies,
        minimum_response=100.0,
    )

    assert ndi.label(repaired == 1, structure=np.ones((3, 3), dtype=bool))[1] == 1
    assert repaired[18, 28] == 1
    assert not np.any(repaired[32, 16:43])


def test_physical_soma_root_mask_distinguishes_attached_and_detached_components():
    owned = np.zeros((32, 48), dtype=np.int32)
    bodies = np.zeros_like(owned)
    bodies[13:20, 3:10] = 1
    owned[16, 10:27] = 1
    owned[5, 34:43] = 1

    rooted = _physically_soma_rooted_owner_mask(
        owned,
        bodies,
        maximum_root_distance=3,
    )

    assert np.all(rooted[16, 10:27])
    assert not np.any(rooted[5, 34:43])


def test_secondary_ownership_adopts_logical_paths_not_whole_components():
    skeleton = np.zeros((33, 33), dtype=bool)
    skeleton[16, 4:29] = True
    skeleton[16:29, 16] = True
    topology = _analyze_topology(
        skeleton,
        np.zeros(skeleton.shape, dtype=np.int32),
        pixel_size_um=1.0,
        outgrowth_width_px=2.0,
    )
    owner_skeleton = np.zeros(skeleton.shape, dtype=np.int32)
    secondary_regions = np.zeros(skeleton.shape, dtype=np.int32)
    secondary_regions[15:18, 3:16] = 1
    secondary_regions[15:18, 17:30] = 2
    secondary_regions[17:30, 15:18] = 3

    adopted = _adopt_secondary_owned_path_segments(
        topology,
        owner_skeleton,
        secondary_regions,
    )

    assert np.all(adopted[16, 4:16] == 1)
    assert np.all(adopted[16, 17:29] == 2)
    assert np.all(adopted[17:29, 16] == 3)
    assert adopted[16, 16] == 0


def test_secondary_ownership_partitions_a_path_at_nominal_owner_boundaries():
    skeleton = np.zeros((24, 32), dtype=bool)
    skeleton[12, 3:29] = True
    topology = _analyze_topology(
        skeleton,
        np.zeros(skeleton.shape, dtype=np.int32),
        pixel_size_um=1.0,
        outgrowth_width_px=2.0,
    )
    secondary_regions = np.zeros(skeleton.shape, dtype=np.int32)
    secondary_regions[11:14, 2:16] = 1
    secondary_regions[11:14, 16:30] = 2

    adopted = _adopt_secondary_owned_path_segments(
        topology,
        np.zeros(skeleton.shape, dtype=np.int32),
        secondary_regions,
    )

    assert np.all(adopted[12, 3:16] == 1)
    assert np.all(adopted[12, 16:29] == 2)


def test_owned_topology_preserves_adjacent_nominal_neuron_paths():
    owned = np.zeros((48, 64), dtype=np.int32)
    bodies = np.zeros_like(owned)
    bodies[20:27, 2:9] = 1
    bodies[20:27, 55:62] = 2
    owned[23, 9:32] = 1
    owned[23, 32:55] = 2

    topology = _analyze_owned_topology(
        owned,
        bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=2.0,
    )
    rendered = np.zeros_like(owned)
    for path_index, coordinates in enumerate(topology.path_coordinates):
        owner = int(topology.path_owners[path_index])
        rendered[tuple(coordinates.T)] = owner

    assert set(topology.path_owners) == {1, 2}
    assert np.all(rendered[23, 9:32] == 1)
    assert np.all(rendered[23, 32:55] == 2)
    assert topology.root_paths_by_cell.keys() == {1, 2}


def test_secondary_path_adoption_survives_only_with_soma_rooted_signal_support():
    shape = (64, 64)
    cell_bodies = np.zeros(shape, dtype=np.int32)
    cell_bodies[29:36, 5:12] = 1
    skeleton = np.zeros(shape, dtype=bool)
    skeleton[32, 30:53] = True
    topology = _analyze_topology(
        skeleton,
        cell_bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=2.0,
    )
    assert not np.any(topology.path_owners)

    def repaired_topology(*, connected: bool):
        owner_regions = np.zeros(shape, dtype=np.int32)
        response = np.zeros(shape, dtype=float)
        owner_regions[32, 30:53] = 1
        response[32, 30:53] = 150.0
        if connected:
            owner_regions[29:36, 5:53] = 1
            response[32, 11:53] = 150.0
        adopted = _adopt_secondary_owned_path_segments(
            topology,
            np.zeros(shape, dtype=np.int32),
            owner_regions,
        )
        assert np.all(adopted[32, 30:53] == 1)
        repaired = _repair_signal_supported_skeleton(
            adopted,
            response,
            owner_regions,
            cell_bodies,
            minimum_response=100.0,
        )
        repaired[cell_bodies > 0] = 0
        return repaired, _analyze_topology(
            repaired > 0,
            cell_bodies,
            pixel_size_um=1.0,
            outgrowth_width_px=2.0,
            assigned_path_labels=repaired,
        )

    disconnected_labels, disconnected_topology = repaired_topology(connected=False)
    assert not np.any(disconnected_labels)
    assert not np.any(disconnected_topology.path_owners)

    connected_labels, connected_topology = repaired_topology(connected=True)
    assert np.all(connected_labels[32, 12:53] == 1)
    assert np.all(connected_topology.path_owners == 1)


def test_signal_supported_repair_bounds_compiled_search_to_owner_regions(monkeypatch):
    shape = (512, 512)
    labels = np.zeros(shape, dtype=np.int32)
    cell_bodies = np.zeros(shape, dtype=np.int32)
    response = np.zeros(shape, dtype=float)
    owner_regions = np.zeros(shape, dtype=np.int32)
    for owner, row, column in ((1, 80, 60), (2, 400, 360)):
        cell_bodies[row - 3 : row + 4, column - 8 : column] = owner
        labels[row, column : column + 8] = owner
        labels[row, column + 50 : column + 58] = owner
        response[row, column : column + 58] = 150.0
        owner_regions[
            row - 20 : row + 21,
            column - 20 : column + 81,
        ] = owner

    observed_shapes = []
    from skimage.graph import MCP_Geometric as CompiledPathFinder

    def record_path_finder(costs, *args, **kwargs):
        observed_shapes.append(costs.shape)
        return CompiledPathFinder(costs, *args, **kwargs)

    monkeypatch.setattr(
        "openhcs.processing.backends.analysis.neurite_outgrowth.MCP_Geometric",
        record_path_finder,
    )

    repaired = _repair_signal_supported_skeleton(
        labels,
        response,
        owner_regions,
        cell_bodies,
        minimum_response=100.0,
    )

    assert len(observed_shapes) == 4
    assert all(
        rows < shape[0] and columns < shape[1] for rows, columns in observed_shapes
    )
    for owner, row, column in ((1, 80, 60), (2, 400, 360)):
        assert (
            ndi.label(
                repaired == owner,
                structure=np.ones((3, 3), dtype=bool),
            )[1]
            == 1
        )
        assert np.all(repaired[row, column : column + 58] == owner)


def test_signal_supported_repair_rejects_unsupported_and_foreign_owner_routes():
    labels = np.zeros((48, 48), dtype=np.int32)
    labels[20, 5:10] = 1
    labels[20, 38:43] = 1
    labels[8:40, 24] = 2
    cell_bodies = np.zeros_like(labels)
    cell_bodies[17:24, 2:8] = 1
    cell_bodies[5:11, 21:28] = 2
    response = np.zeros(labels.shape, dtype=float)
    response[20, 5:43] = 150.0
    response[labels > 0] = 150.0
    owner_regions = np.zeros_like(labels)
    owner_regions[20, 5:24] = 1
    owner_regions[20, 25:43] = 1
    owner_regions[8:40, 24] = 2
    owner_regions[cell_bodies > 0] = cell_bodies[cell_bodies > 0]

    repaired = _repair_signal_supported_skeleton(
        labels,
        response,
        owner_regions,
        cell_bodies,
        minimum_response=100.0,
    )

    assert np.all(repaired[20, 5:10] == 1)
    assert not np.any(repaired[20, 38:43] == 1)
    assert np.all(repaired[8:40, 24] == 2)
    assert not np.any(repaired[:, 24] == 1)


def test_topology_discards_assigned_paths_detached_from_the_soma():
    labels = np.zeros((32, 32), dtype=np.int32)
    labels[16, 9:16] = 1
    labels[5, 20:26] = 1
    cell_bodies = np.zeros_like(labels)
    rows, columns = disk((16, 5), 4, shape=labels.shape)
    cell_bodies[rows, columns] = 1

    topology = _analyze_topology(
        labels > 0,
        cell_bodies,
        pixel_size_um=1.0,
        outgrowth_width_px=3.0,
        assigned_path_labels=labels,
    )
    owned_skeleton = np.zeros_like(labels)
    for path_index, coordinates in enumerate(topology.path_coordinates):
        if topology.path_owners[path_index] == 1:
            owned_skeleton[tuple(coordinates.T)] = 1

    assert np.all(owned_skeleton[16, 9:16] == 1)
    assert not np.any(owned_skeleton[5, 20:26])


def test_rejects_a_plain_2d_image_because_channels_must_be_explicit():
    with pytest.raises(ValueError, match="2D channel stack"):
        _implementation()(np.zeros((32, 32)), pixel_size=1.0)


def test_morphology_retains_topology_owners_when_shared_endpoints_collide():
    from openhcs.processing.backends.analysis.neurite_outgrowth import (
        _render_owned_skeleton,
    )

    paths = (
        np.array([[2, 2], [2, 3]], dtype=int),
        np.array([[2, 2], [3, 2], [2, 3]], dtype=int),
    )
    topology = _TopologyResult(
        path_owners=np.array([1, 2], dtype=np.int32),
        path_distances=np.zeros(2),
        path_lengths=np.array([1.0, 1.0 + np.sqrt(2.0)]),
        path_euclidean_lengths=np.ones(2),
        path_coordinates=paths,
        path_endpoint_groups=((1, 2), (1, 2)),
        path_branch_types=np.zeros(2, dtype=np.int32),
        endpoint_group_coordinates={1: (2.0, 2.0), 2: (2.0, 3.0)},
        transitions={0: (1,), 1: (0,)},
        root_paths_by_cell={1: (0,), 2: (1,)},
        branch_nodes_by_cell={},
        crossing_nodes=frozenset(),
        crossing_paths=frozenset(),
        crossing_core_paths=frozenset(),
    )
    bodies = np.zeros((8, 8), dtype=np.int32)
    bodies[1, 2] = 1
    bodies[4, 2] = 2

    # A scalar raster cannot encode both owners at their shared endpoints.
    rendered = _render_owned_skeleton(bodies.shape, topology)
    assert rendered[tuple(paths[1].T)].tolist() == [1, 2, 1]

    graph = _build_neurite_morphology_graph(
        topology, bodies, pixel_size_um=1.0, outgrowth_width_px=1.0
    )
    graph.require_directed_forest()
    assert len(graph.edges) == 2
    for owner, expected_length in ((1, 1.0), (2, 1.0 + np.sqrt(2.0))):
        owned_edges = [
            edge
            for edge in graph.edges
            if edge.feature_mapping()["neuron_label"] == owner
        ]
        assert len(owned_edges) == 1
        assert owned_edges[0].feature_mapping()["branch_distance_um"] == (
            pytest.approx(expected_length)
        )
        assert np.asarray(owned_edges[0].coordinates) == pytest.approx(paths[owner - 1])
