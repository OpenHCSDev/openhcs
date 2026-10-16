"""Shared source-plan declarations own normalization without consuming directives."""
from dataclasses import fields
from typing import get_type_hints

import pytest

from objectstate import DataclassFieldAccess, LazyDataclassFactory
from objectstate.field_value import Inherit, Unset
from openhcs.core.config import SourceBindingsConfig
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan, NamedSourceBinding, SourceBindingDeclarationsMixin,
)


@pytest.mark.parametrize("meaning", [Inherit(), Unset()])
def test_normalization_preserves_directive_fields(meaning):
    lazy = LazyDataclassFactory.make_lazy_simple(SourceBindingsConfig)
    config = lazy(
        metadata_rules=meaning, match_plan=meaning, metadata_fields=meaning,
        bindings=meaning, source_stack_components=meaning, source_filters=meaning,
        image_plane_sources=meaning, imported_metadata_tables=meaning,
        grouping_metadata_fields=meaning, source_voxel_spacing=meaning,
    )
    with pytest.raises(TypeError):
        CompiledSourceBindingPlan(bindings=meaning)
    for name in (
        "metadata_rules", "match_plan", "metadata_fields", "bindings",
        "source_stack_components", "source_filters", "image_plane_sources",
        "imported_metadata_tables", "grouping_metadata_fields", "source_voxel_spacing",
    ):
        assert DataclassFieldAccess.raw_value(config, name) == meaning


@pytest.mark.parametrize("owner", [SourceBindingsConfig, CompiledSourceBindingPlan])
def test_common_normalization_and_duplicate_validation_are_inherited(owner):
    binding = NamedSourceBinding(alias="DNA")
    config = owner(bindings=[binding], source_stack_components=[])
    assert config.bindings == (binding,)
    assert config.source_stack_components == ()
    with pytest.raises(ValueError, match="duplicate alias"):
        owner(bindings=[binding, binding])
    with pytest.raises(TypeError, match="must be NamedSourceBinding"):
        owner(bindings=["not a binding"])
    with pytest.raises(TypeError):
        owner(bindings=None)


def test_binding_view_inherits_its_one_field_declaration():
    assert "bindings" not in SourceBindingDeclarationsMixin.__annotations__
    expected = tuple[NamedSourceBinding, ...]
    assert get_type_hints(SourceBindingDeclarationsMixin)["bindings"] == expected
    assert get_type_hints(SourceBindingsConfig)["bindings"] == expected
    assert get_type_hints(CompiledSourceBindingPlan)["bindings"] == expected
    base_fields = {item.name: item for item in fields(SourceBindingDeclarationsMixin)}
    for owner in (SourceBindingsConfig, CompiledSourceBindingPlan):
        declared = {item.name: item for item in fields(owner)}
        for name in ("bindings", "source_stack_components", "source_spatial_domain"):
            assert declared[name] is base_fields[name]
