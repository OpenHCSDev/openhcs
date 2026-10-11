"""K1 guards: plane modes are families and their absence is a member, not None.

``RuntimePlaneAxis`` (with ``NoPlaneAxis``), ``ObjectLabelDomainScope`` and the
whole-axis / selected-plane projections are class families. Callers ask a
member (``leads_data``, ``one_plane_per_runtime_slice``, ``ids_per_plane``,
``selects_one_plane``) or call its methods; they never compare against a
member or against ``None``.
"""

from __future__ import annotations

import ast
from dataclasses import fields
from functools import lru_cache
from pathlib import Path

import pytest

from openhcs.core.runtime_object_label_domains import ObjectLabelDomainScope
from openhcs.core.runtime_plane_projection import (
    NoPlaneAxis,
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
    RuntimePlaneProjection,
    RuntimeSliceProjectableValue,
    SelectedPlaneProjection,
    StackPlaneSelection,
    WholeAxisProjection,
    WholeStackProjection,
)

ROOT = Path(__file__).resolve().parents[2]
OPENHCS = ROOT / "openhcs"

DELETED_NAMES = {
    "ImagePayloadMetadataCompositionMode",
    "RuntimePlaneAxisStrategy",
    "RuntimeSlicePlaneAxisStrategy",
    "SourceBindingPlaneAxisStrategy",
    "ObjectLabelPlaneDomainStrategy",
    "PayloadObjectLabelPlaneDomainStrategy",
    "PlaneObjectLabelPlaneDomainStrategy",
    "image_metadata_of",
    "array_data_of",
}


@lru_cache(maxsize=1)
def _trees() -> dict[str, ast.Module]:
    return {
        path.relative_to(ROOT).as_posix(): ast.parse(path.read_text(encoding="utf-8"))
        for path in sorted(OPENHCS.rglob("*.py"))
    }


def _member_names() -> frozenset[str]:
    """Every member class of the two plane-mode families, from their registries."""
    return frozenset(
        member.__name__
        for family in (RuntimePlaneAxis, ObjectLabelDomainScope)
        for member in family.__registry__.values()
    )


def _names(node: ast.AST) -> set[str]:
    return {
        child.id if isinstance(child, ast.Name) else child.attr
        for child in ast.walk(node)
        if isinstance(child, ast.Name | ast.Attribute)
    }


def test_deleted_plane_mode_names_are_gone() -> None:
    found = sorted(
        f"{module}:{node.lineno}:{name}"
        for module, tree in _trees().items()
        for node in ast.walk(tree)
        for name in (
            getattr(node, "id", None),
            getattr(node, "attr", None),
            getattr(node, "name", None),
        )
        if name in DELETED_NAMES
    )
    assert not found, "\n".join(found)


def test_no_code_compares_against_a_plane_mode_member() -> None:
    members = _member_names()
    assert {"NoPlaneAxis", "PayloadLabelScope"} <= members
    found = sorted(
        f"{module}:{node.lineno}"
        for module, tree in _trees().items()
        for node in ast.walk(tree)
        if isinstance(node, ast.Compare)
        and any(
            isinstance(operand, ast.Name | ast.Attribute | ast.Tuple | ast.List | ast.Set)
            and _names(operand) & members
            for operand in (node.left, *node.comparators)
        )
    )
    assert not found, "\n".join(found)


def test_no_plane_axis_is_compared_with_none() -> None:
    def is_plane_axis(node: ast.expr) -> bool:
        name = (
            node.id if isinstance(node, ast.Name)
            else node.attr if isinstance(node, ast.Attribute)
            else ""
        )
        # ``indexed_source_plane_axis`` is a component name in materialization (K8).
        return name.endswith("plane_axis") and name != "indexed_source_plane_axis"

    found = sorted(
        f"{module}:{node.lineno}"
        for module, tree in _trees().items()
        for node in ast.walk(tree)
        if isinstance(node, ast.Compare)
        and is_plane_axis(node.left)
        and any(
            isinstance(comparator, ast.Constant) and comparator.value is None
            for comparator in node.comparators
        )
    )
    assert not found, "\n".join(found)


def test_no_projection_plane_index_is_compared_with_none() -> None:
    found = sorted(
        f"{module}:{node.lineno}"
        for module, tree in _trees().items()
        for node in ast.walk(tree)
        if isinstance(node, ast.Compare)
        and isinstance(node.left, ast.Attribute)
        and node.left.attr == "plane_index"
        and isinstance(node.left.value, ast.Name | ast.Attribute)
        and (
            node.left.value.id
            if isinstance(node.left.value, ast.Name)
            else node.left.value.attr
        ).endswith("projection")
        and any(
            isinstance(comparator, ast.Constant) and comparator.value is None
            for comparator in node.comparators
        )
    )
    assert not found, "\n".join(found)


def test_plane_index_exists_only_on_the_selecting_members() -> None:
    def field_names(cls: type) -> set[str]:
        return {member.name for member in fields(cls)}

    assert "plane_index" not in field_names(WholeAxisProjection)
    assert "plane_index" not in field_names(WholeStackProjection)
    assert "plane_index" in field_names(SelectedPlaneProjection)
    assert "plane_index" in field_names(StackPlaneSelection)
    for family in (RuntimePlaneAxisValueProjection, RuntimePlaneProjection):
        with pytest.raises(TypeError):
            family()  # abstract: every projection is one of the two members


def test_every_plane_axis_answers_the_family_questions() -> None:
    assert set(RuntimePlaneAxis.leading_axes()) == {
        axis for axis in RuntimePlaneAxis.__registry__.values() if axis.leads_data
    }
    assert NoPlaneAxis not in RuntimePlaneAxis.leading_axes()
    for name, axis in RuntimePlaneAxis.__registry__.items():
        assert RuntimePlaneAxis.named(name) is axis
        assert axis.axis_when_stacked().leads_data
        assert (
            axis.one_plane_per_runtime_slice + axis.one_plane_per_source_binding
            == axis.leads_data
        )
    for scope in ObjectLabelDomainScope.__registry__.values():
        assert isinstance(scope.ids_per_plane, bool)


def test_image_metadata_and_array_data_are_runtime_value_methods() -> None:
    for name in (
        "image_metadata",
        "array_data",
        "slice_source_provenances",
        "scalar_source_provenance",
    ):
        assert name in vars(RuntimeSliceProjectableValue)
