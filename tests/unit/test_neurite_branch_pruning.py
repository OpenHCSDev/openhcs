"""Length pruning uses outward continuation, not individual edge length."""

from collections import defaultdict
from dataclasses import replace

import numpy as np
import pytest
from skimage.draw import line

from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    MetaXpressOutgrowthSettings, PixelOutgrowthSettings, _TopologyResult,
    _build_cell_results, _build_neurite_morphology_graph, _render_owned_skeleton,
)


def topology_for(points, edges, *, scale=1.0):
    paths = tuple(np.column_stack(line(*points[a], *points[b])) for a, b in edges)
    incidence = defaultdict(list)
    for i, ends in enumerate(edges):
        for node in ends:
            incidence[node].append(i)
    transitions = {
        i: tuple(sorted({n for node in ends for n in incidence[node] if n != i}))
        for i, ends in enumerate(edges)
    }
    bodies = np.zeros((64, 64), dtype=np.int32)
    bodies[23:26, 1:4] = 1
    support = np.zeros_like(bodies, dtype=bool)
    for p in paths:
        support[tuple(p.T)] = True
    topology = _TopologyResult(
        path_owners=np.ones(len(edges), dtype=np.int32),
        path_distances=np.zeros(len(edges)), coordinate_scale=scale,
        path_coordinates=paths, path_endpoint_groups=tuple(edges),
        path_branch_types=np.zeros(len(edges), dtype=np.int32),
        endpoint_group_coordinates=points, transitions=transitions,
        root_paths_by_cell={1: (0,)}, branch_nodes_by_cell={}, resolved_crossings=(),
    )
    return topology, bodies, support


def prune(topology, bodies, support, minimum):
    return topology.prune_short_branches(
        minimum, cell_body_labels=bodies, branch_support=support, outgrowth_width_px=1,
    )


@pytest.mark.parametrize('settings', [MetaXpressOutgrowthSettings, PixelOutgrowthSettings])
@pytest.mark.parametrize('value', [-1, np.nan, np.inf, True])
def test_invalid_branch_length_is_rejected_even_without_enhancement(settings, value):
    with pytest.raises(ValueError, match='minimum_branch_length'):
        settings(minimum_branch_length=value, enhance_neurites=False).validate()


def test_disabled_pruning_preserves_the_original_topology():
    t, b, s = topology_for({0: (24, 4), 1: (24, 14), 2: (24, 44), 3: (20, 14)},
                          [(0, 1), (1, 2), (1, 3)])
    assert MetaXpressOutgrowthSettings().minimum_branch_length == 0
    assert prune(t, b, s, 0) is t


@pytest.mark.parametrize('scale', [1.0, 1.3556, 2.0])
def test_short_tooth_is_removed_from_graph_image_and_measurements(scale):
    t, b, s = topology_for({0: (24, 4), 1: (24, 14), 2: (24, 44), 3: (20, 14)},
                          [(0, 1), (1, 2), (1, 3)], scale=scale)
    result = prune(t, b, s, 5 * scale)
    np.testing.assert_array_equal(result.path_owners, [1, 1, 0])
    np.testing.assert_array_equal(t.path_owners, [1, 1, 1])
    assert result.root_paths_by_cell == {1: (0,)}
    assert not result.branch_nodes_by_cell.get(1)
    assert result.transitions == {0: (1,), 1: (0,), 2: ()}
    rendered = _render_owned_skeleton(b.shape, result)
    assert not np.any(rendered[20:24, 14])
    assert np.all(rendered[24, 4:45] == 1)
    spacing = SourceVoxelSpacing((scale, scale))
    rows = _build_cell_results(b, rendered, rendered, np.ones(b.shape), result,
                               10, spacing, slice_index=0)
    assert rows[0].total_outgrowth == pytest.approx(40 * scale)
    assert rows[0].branches == 0
    assert rows[0].processes == 1
    graph = _build_neurite_morphology_graph(result, b, coordinate_spacing=spacing,
                                           outgrowth_width_px=1)
    assert len(graph.edges) == 2
    assert sum(e.feature_mapping()['branch_distance'] for e in graph.edges) == pytest.approx(40 * scale)


def test_short_segments_accumulate_and_threshold_equality_is_retained():
    t, b, s = topology_for(
        {0: (24, 4), 1: (24, 14), 2: (24, 17), 3: (24, 21), 4: (22, 14)},
        [(0, 1), (1, 2), (2, 3), (1, 4)],
    )
    np.testing.assert_array_equal(prune(t, b, s, 7).path_owners, [1, 1, 1, 0])


def test_multiple_daughters_cannot_pool_their_lengths_to_qualify():
    t, b, s = topology_for(
        {0: (24, 4), 1: (24, 14), 2: (24, 44), 3: (23, 14), 4: (23, 11), 5: (23, 17)},
        [(0, 1), (1, 2), (1, 3), (3, 4), (3, 5)],
    )
    # The two daughters total six, but the longest outward route is only 1+3.
    np.testing.assert_array_equal(prune(t, b, s, 5).path_owners, [1, 1, 0, 0, 0])


def test_soma_paths_and_loops_are_preserved_but_a_loop_tooth_is_pruned():
    t, b, s = topology_for(
        {0: (24, 4), 1: (24, 14), 2: (24, 17), 3: (27, 17), 4: (27, 14), 5: (22, 17)},
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 1), (2, 5)],
    )
    np.testing.assert_array_equal(prune(t, b, s, 100).path_owners, [1, 1, 1, 1, 1, 0])


def test_owner_identity_prevents_borrowing_a_foreign_continuation():
    t, b, s = topology_for({0: (24, 4), 1: (24, 14), 2: (24, 44), 3: (20, 14)},
                          [(0, 1), (1, 2), (1, 3)])
    # Same geometric group numbers, distinct neurons: owner 2 cannot qualify
    # owner 1's short arm, and its independent soma path must survive.
    t = replace(t, path_owners=np.array([1, 1, 1, 2]),
                path_distances=np.zeros(4),
                path_coordinates=t.path_coordinates + (t.path_coordinates[1],),
                path_endpoint_groups=t.path_endpoint_groups + ((3, 2),),
                path_branch_types=np.zeros(4, dtype=np.int32),
                root_paths_by_cell={1: (0,), 2: (3,)},
                transitions={**t.transitions, 3: ()})
    b[28:30, 14:16] = 2
    np.testing.assert_array_equal(prune(t, b, s, 5).path_owners, [1, 1, 0, 2])


def test_standalone_short_soma_process_is_removed_without_removing_the_cell():
    t, b, s = topology_for({0: (24, 4), 1: (23, 5)}, [(0, 1)])
    result = prune(t, b, s, 5)
    assert result.path_owners.tolist() == [0]
    assert result.root_paths_by_cell == {1: ()}
    assert not _render_owned_skeleton(b.shape, result).any()
    assert not _build_neurite_morphology_graph(
        result, b, coordinate_spacing=SourceVoxelSpacing((1., 1.)), outgrowth_width_px=1,
    ).edges
    rendered = _render_owned_skeleton(b.shape, result)
    rows = _build_cell_results(b, rendered, rendered, np.ones(b.shape), result,
                              10, SourceVoxelSpacing((1., 1.)), slice_index=0)
    assert len(rows) == 1
    assert rows[0].processes == rows[0].total_outgrowth == 0


def test_short_root_is_kept_when_its_outward_continuation_is_long():
    t, b, s = topology_for({0: (24, 4), 1: (24, 5), 2: (24, 15)}, [(0, 1), (1, 2)])
    np.testing.assert_array_equal(prune(t, b, s, 5).path_owners, [1, 1])


def test_short_complete_root_tree_uses_longest_path_not_total_daughters():
    t, b, s = topology_for(
        {0: (24, 4), 1: (24, 5), 2: (21, 5), 3: (27, 5)}, [(0, 1), (1, 2), (1, 3)],
    )
    assert not prune(t, b, s, 5).path_owners.any()


@pytest.mark.parametrize('value', [-1, np.nan, np.inf, True])
def test_invalid_smoothing_is_rejected_even_without_enhancement(value):
    with pytest.raises(ValueError, match='centerline_smoothing_sigma_px'):
        MetaXpressOutgrowthSettings(centerline_smoothing_sigma_px=value, enhance_neurites=False).validate()


@pytest.mark.parametrize('scale', [1.0, 1.3556, 2.0])
def test_subpixel_geometry_corrects_staircase_length_and_agrees_with_export(scale):
    t, b, s = topology_for({0: (24, 4), 1: (44, 44)}, [(0, 1)], scale=scale)
    refined = replace(t, centerline_smoothing_sigma_px=1.0)
    curve = refined.path_centerline(0)
    assert np.any(curve != np.round(curve))
    np.testing.assert_array_equal(curve[[0, -1]], t.path_coordinates[0][[0, -1]])
    assert np.linalg.norm(curve - t.path_coordinates[0], axis=1).max() <= 0.5 + 1e-12
    ideal = np.hypot(20, 40) * scale
    assert refined.path_lengths[0] < t.path_lengths[0]
    assert refined.path_lengths[0] == pytest.approx(ideal, rel=.01)
    graph = _build_neurite_morphology_graph(refined, b, coordinate_spacing=SourceVoxelSpacing((scale, scale)), outgrowth_width_px=1)
    edge = graph.edges[0]
    measured = np.linalg.norm(np.diff(edge.coordinates, axis=0), axis=1).sum() * scale
    assert edge.feature_mapping()['branch_distance'] == pytest.approx(measured)
    rendered = _render_owned_skeleton(b.shape, refined)
    rows = _build_cell_results(b, rendered, rendered, np.ones(b.shape), refined,
                              10, SourceVoxelSpacing((scale, scale)), slice_index=0)
    assert rows[0].total_outgrowth == pytest.approx(measured)
    np.testing.assert_array_equal(rendered, _render_owned_skeleton(b.shape, t))


def test_smoothing_preserves_axis_diagonal_bends_and_cycle_closure():
    for end in [(24, 44), (44, 24)]:
        t, _, _ = topology_for({0: (24, 4), 1: end}, [(0, 1)])
        refined = replace(t, centerline_smoothing_sigma_px=1.0)
        np.testing.assert_allclose(refined.path_centerline(0), t.path_coordinates[0], atol=1e-12)
    # A right-angle bend and a ring cannot be replaced by endpoint chords.
    t, _, _ = topology_for({0: (24, 4), 1: (44, 24)}, [(0, 1)])
    bend = np.r_[np.column_stack((np.full(21, 24), np.arange(4, 25))),
                 np.column_stack((np.arange(25, 45), np.full(20, 24)))]
    t = replace(t, path_coordinates=(bend,), centerline_smoothing_sigma_px=1.0)
    assert 39 < t.path_lengths[0] <= 40
    ring = np.r_[bend, np.column_stack((np.full(20, 44), np.arange(23, 3, -1))),
                 np.column_stack((np.arange(43, 23, -1), np.full(20, 4)))]
    t = replace(t, path_coordinates=(ring,), path_endpoint_groups=((0, 0),))
    np.testing.assert_array_equal(t.path_centerline(0)[0], t.path_centerline(0)[-1])
    assert 76 < t.path_lengths[0] <= 80
