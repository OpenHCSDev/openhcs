"""N1 guards: a resolved crossing is shared by every neuron passing through it."""

import ast
import inspect

import numpy as np

import openhcs.processing.backends.analysis.neurite_outgrowth as neurite
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    NeuriteTopologyClass,
    _empty_topology,
)


def _called_names(function) -> set[str]:
    tree = ast.parse(inspect.getsource(function))
    return {
        node.func.attr if isinstance(node.func, ast.Attribute) else getattr(node.func, "id", "")
        for node in ast.walk(tree) if isinstance(node, ast.Call)
    }


def test_final_topology_routes_owners_through_the_crossing_instead_of_lending_the_core():
    # Lending only the raster core made each owner detour around the crossing.
    called = _called_names(neurite._analyze_owned_topology)
    assert "crossing_routes" in called
    assert "crossing_support_mask" not in called


def test_crossing_count_and_label_image_come_from_the_topology():
    source = inspect.getsource(neurite)
    # Counted from the crossing declaration, not from raster adjacency.
    assert "_count_multi_owner_crossings" not in source
    # The trace image is rendered from the topology only, never overwritten
    # with a nearest-owner core raster.
    assert "crossing_core_support" not in source


def test_topology_classes_are_one_family_and_a_new_class_needs_one_declaration():
    table = NeuriteTopologyClass.value_table()
    assert table == {
        "none": 0, "path": 1, "endpoint": 2, "soma_attachment": 3,
        "branch_point": 4, "crossing": 5,
    }

    class TopologyProbe(NeuriteTopologyClass):
        plane_value = 250

        @staticmethod
        def pixels(topology, cell_body_labels):
            return np.array([[1, 2]])

    try:
        assert NeuriteTopologyClass.value_table()["probe"] == 250
        plane = NeuriteTopologyClass.render(_empty_topology(), np.zeros((4, 4), dtype=np.int32))
        assert plane[1, 2] == 250
    finally:
        del NeuriteTopologyClass.__registry__[250]
