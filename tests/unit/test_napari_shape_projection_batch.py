"""Native shape projections for the isolated dependency source patch."""

import numpy as np
import pytest

from napari.layers import Shapes
from napari.components import Dims
from napari.layers.shapes._shape_list import ShapeList
from napari.layers.shapes._shapes_models import Ellipse, Line, Path, Polygon, Rectangle

pytestmark = pytest.mark.skipif(
    not hasattr(ShapeList, "_rebuild_meshes"),
    reason="Isolated Napari source-patch qualification; inherited installation stays unchanged",
)


@pytest.mark.parametrize("model_type", [Ellipse, Line, Path, Polygon, Rectangle])
def test_hidden_order_retains_subtype_geometry_and_rounding(model_type):
    spatial = np.array([[1, 1], [1, 8], [8, 8], [8, 1]], dtype=float)
    if model_type is Line:
        spatial = spatial[:2]
    data = np.column_stack((np.full(len(spatial), 2.2), np.full(len(spatial), 3.6), spatial))
    model = model_type(data, dims_order=[0, 1, 2, 3])
    original_data = model.data.copy()
    key = model.slice_key.copy()
    faces, edges, box = model._face_vertices, model._edge_vertices, model._box
    model.dims_order = (1, 0, 2, 3)
    np.testing.assert_array_equal(model.slice_key, key[:, [1, 0]])
    assert model._face_vertices is faces and model._edge_vertices is edges and model._box is box
    np.testing.assert_array_equal(model.data, original_data)


def test_mesh_rebuild_preserves_identity_and_all_projections():
    data = np.array([[2, 4, 1, 1], [2, 4, 1, 8], [2, 4, 8, 8], [2, 4, 8, 1]], dtype=float)
    models = [Polygon(data, z_index=2), Rectangle(data + [0, 0, 12, 12], z_index=1)]
    shapes = ShapeList()
    shapes.slice_key = [2, 4]
    shapes.add(models, face_color=np.array([[1, 0, 0, 1], [0, 1, 0, 1]]),
               edge_color=np.array([[0, 0, 1, 1], [1, 1, 0, 1]]))
    original_list, mesh = shapes.shapes, shapes._mesh
    colors = shapes._face_color.copy(), shapes._edge_color.copy()
    for order, ndisplay in [((1, 0, 2, 3), 2), ((1, 0, 3, 2), 2), ((1, 0, 3, 2), 3), ((0, 1, 2, 3), 2)]:
        with shapes.batched_updates():
            shapes.ndisplay = ndisplay
            shapes.update_dims_order(order)
            shapes.slice_key = models[0].slice_key[0]
        assert shapes.shapes is original_list and shapes._mesh is mesh
        assert all(actual is original for actual, original in zip(shapes.shapes, models, strict=True))
        expected = ShapeList(ndisplay=ndisplay)
        expected.slice_key = shapes.slice_key
        expected.add(models, face_color=colors[0], edge_color=colors[1])
        for name in ("_vertices", "_index", "_z_index", "_face_color", "_edge_color", "_z_order"):
            np.testing.assert_array_equal(getattr(shapes, name), getattr(expected, name))
        for name in ("vertices", "vertices_centers", "vertices_offsets", "vertices_index", "triangles", "triangles_index", "triangles_colors", "displayed_triangles", "displayed_triangles_colors"):
            np.testing.assert_array_equal(getattr(mesh, name), getattr(expected._mesh, name))


def test_hidden_order_preserves_selection_but_changed_field_does_not():
    data = np.array([[2, 4, 1, 1], [2, 4, 1, 8], [2, 4, 8, 8], [2, 4, 8, 1]], dtype=float)
    layer = Shapes([data], shape_type="polygon")
    layer._slice_dims(Dims(ndim=4, range=((0, 20, 1),) * 4, point=(2, 4, 0, 0)))
    layer.selected_data = {0}
    layer._slice_dims(Dims(ndim=4, range=((0, 20, 1),) * 4, order=(1, 0, 2, 3), point=(2, 4, 0, 0)))
    assert layer.selected_data == {0}
    layer._slice_dims(Dims(ndim=4, range=((0, 20, 1),) * 4, order=(1, 0, 2, 3), point=(3, 4, 0, 0)))
    assert layer.selected_data == set()


@pytest.mark.parametrize("slice_key", [(0, 0), (2, 4), (8, 9)])
def test_displayed_projection_retains_original_draw_order_and_colors(slice_key):
    data = np.array([[2, 4, 1, 1], [2, 4, 1, 8], [2, 4, 8, 8], [2, 4, 8, 1]], dtype=float)
    models = [Polygon(data, z_index=2), Polygon(data + [6, 5, 0, 0], z_index=0),
              Rectangle(data + [0, 0, 12, 12], z_index=1)]
    shapes = ShapeList()
    shapes.slice_key = slice_key
    shapes.add(models, face_color=np.eye(4)[:3], edge_color=np.eye(4)[1:])
    mesh = shapes._mesh
    visible_shapes = np.where(shapes._displayed)[0]
    z_order = mesh.triangles_z_order
    visible_triangles = np.isin(mesh.triangles_index[z_order, 0], visible_shapes)
    for source, projected in [("triangles", "displayed_triangles"),
                              ("triangles_index", "displayed_triangles_index"),
                              ("triangles_colors", "displayed_triangles_colors")]:
        np.testing.assert_array_equal(getattr(mesh, projected),
                                      getattr(mesh, source)[z_order][visible_triangles])
    visible_vertices = np.isin(shapes._index, visible_shapes)
    np.testing.assert_array_equal(shapes.displayed_vertices, shapes._vertices[visible_vertices])
    np.testing.assert_array_equal(shapes.displayed_index, shapes._index[visible_vertices])
