"""G3 guards: the tensor payload family owns its answers; the old switches stay gone."""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PRODUCT = ROOT / "openhcs"

DELETED_FUNCTIONS = {
    "image_payload_data",
    "image_payload_metadata",
    "image_payload_mask",
    "image_payload_geometry",
    "with_image_payload_data",
    "image_payload_slice_context",
    "image_payload_mask_for_slice",
    "image_mask_for_data_domain",
    "image_payload_intensity_scale",
    "normalize_image_payload_intensity",
    "payload_slices_for_alignment",
    "flatten_aligned_image_payload_slices",
    "payload_slice_count",
    "project_declared_source_identity",
    "is_grayscale_image_slice",
    "is_color_image_slice",
    "image_spatial_axis_indices",
    "image_spatial_shape_yx",
}
DELETED_NAMES = {
    "ImagePayloadMetadataCarrier",
    "RuntimeSliceProjectionStrategy",
    "ImageOutputSourceContextStrategy",
    "ObjectLabelOutputValueContextStrategy",
    "ObjectLocationCoordinateProjectionStrategy",
    "ImageShapeRole",
    "ArrayShape",
}
DELETED_METADATA_MEMBERS = {
    "normalized_source_channel_axis",
    "without_source_channel_axis",
    "is_declared_source_channel_plane",
    "is_declared_source_channel_stack",
    "channel_axis_without_leading_plane",
    "non_channel_axes",
}
OWNED_MODULES = (
    "core/runtime_image_values.py",
    "core/aligned_image_payload.py",
    "core/projected_image_output.py",
    "core/image_shapes.py",
    "core/runtime_plane_projection.py",
    "core/runtime_slice_projection.py",
    "core/runtime_array_values.py",
    "core/source_spatial_domain.py",
    "core/payload_axes.py",
    "core/artifacts.py",
    "core/steps/function_runtime.py",
)


def _product_trees() -> list[tuple[Path, ast.Module]]:
    return [
        (path, ast.parse(path.read_text(encoding="utf-8"), filename=str(path)))
        for path in sorted(PRODUCT.rglob("*.py"))
    ]


@pytest.fixture(scope="module")
def product_trees() -> list[tuple[Path, ast.Module]]:
    return _product_trees()


def _violations(trees, predicate) -> list[str]:
    return [
        f"{path.relative_to(ROOT)}:{node.lineno}"
        for path, tree in trees
        for node in ast.walk(tree)
        if predicate(node)
    ]


def test_bare_or_payload_accessors_do_not_exist(product_trees) -> None:
    def defines_or_calls(node: ast.AST) -> bool:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return node.name in DELETED_FUNCTIONS
        if isinstance(node, ast.Name):
            return node.id in DELETED_FUNCTIONS
        if isinstance(node, ast.alias):
            return node.name in DELETED_FUNCTIONS
        return False

    assert _violations(product_trees, defines_or_calls) == []


def test_replaced_families_and_carrier_name_do_not_exist(product_trees) -> None:
    def names_deleted(node: ast.AST) -> bool:
        if isinstance(node, ast.ClassDef):
            return node.name in DELETED_NAMES
        if isinstance(node, ast.Name):
            return node.id in DELETED_NAMES
        if isinstance(node, ast.alias):
            return node.name in DELETED_NAMES
        return False

    assert _violations(product_trees, names_deleted) == []


def test_metadata_declares_axes_not_one_channel_slot(product_trees) -> None:
    from openhcs.core.runtime_image_values import ImagePayloadMetadata

    assert "source_channel_axis" not in {
        field.name for field in ImagePayloadMetadata.__dataclass_fields__.values()
    }

    def uses_channel_slot(node: ast.AST) -> bool:
        return isinstance(node, ast.Attribute) and node.attr in DELETED_METADATA_MEMBERS

    assert _violations(product_trees, uses_channel_slot) == []


def test_owned_modules_have_no_hand_written_slice_loops() -> None:
    """Slice values come from ``values``/``map_slices``; only their definition loops."""
    def is_slice_count_range(node: ast.AST) -> bool:
        return (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "range"
            and len(node.args) == 1
            and isinstance(node.args[0], ast.Attribute)
            and node.args[0].attr == "slice_count"
        )

    violations = []
    for relative in OWNED_MODULES:
        path = PRODUCT / relative
        tree = ast.parse(path.read_text(encoding="utf-8"))
        violations.extend(
            f"{relative}:{node.lineno}" for node in ast.walk(tree) if is_slice_count_range(node)
        )
    assert violations == []


def test_location_and_sparse_label_names_derive_from_the_spatial_domain() -> None:
    from openhcs.core.runtime_measurements import object_location_features
    from openhcs.core.runtime_sparse_labels import SparseIJVLabelRows
    from openhcs.core.source_spatial_domain import (
        SourceSpatialDomain,
        VolumeSourceSpatialDomain,
    )

    assert tuple(feature.value for feature in object_location_features()) == tuple(
        f"center_{name}" for name in reversed(VolumeSourceSpatialDomain.axis_names)
    )
    assert tuple(
        field.name for field in SparseIJVLabelRows.YX_LABEL_FIELDS[:-1]
    ) == SourceSpatialDomain.axis_names
    for relative in ("core/runtime_measurements.py", "core/runtime_sparse_labels.py"):
        tree = ast.parse((PRODUCT / relative).read_text(encoding="utf-8"))
        spelled = {
            node.value
            for node in ast.walk(tree)
            if isinstance(node, ast.Constant)
            and node.value in {"center_x", "center_y", "center_z", "y", "x"}
        }
        assert spelled == set(), (relative, spelled)
