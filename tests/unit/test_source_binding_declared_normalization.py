"""Shared source-plan declarations own normalization without consuming directives."""
from dataclasses import dataclass, field, fields
from typing import get_type_hints

import pytest

from python_introspect import DataclassPostInit
from objectstate import DataclassFieldAccess, LazyDataclassFactory
from objectstate.field_value import Inherit, Unset
from openhcs.core.config import SourceBindingsConfig
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan, NamedSourceBinding, SourceBindingDeclarationsMixin,
    SourceFieldTransform,
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


def test_new_field_normalizes_and_validates_without_a_roster_edit():
    @dataclass(frozen=True)
    class ExtendedPlan(CompiledSourceBindingPlan):
        names: tuple[str, ...] = ()

    assert ExtendedPlan(names=["DNA"]).names == ("DNA",)
    with pytest.raises(TypeError, match=r"names\[0\].*str"):
        ExtendedPlan(names=[3])


def test_extra_behavior_is_declared_on_the_new_field():
    @dataclass(frozen=True)
    class ExtendedPlan(CompiledSourceBindingPlan):
        names: tuple[str, ...] = field(default=(), metadata={
            SourceFieldTransform: SourceFieldTransform(
                lambda owner, values: tuple(value.strip() for value in values)
            ),
        })

    assert ExtendedPlan(names=[" DNA "]).names == ("DNA",)


def test_post_init_uses_c3_and_runs_the_next_capability_once():
    events = []

    class TrailingInit(DataclassPostInit):
        def __post_init__(self):
            assert type(self.bindings) is tuple or self.bindings == Inherit()
            events.append("trailing")
            super().__post_init__()

    @dataclass(frozen=True)
    class ExtendedPlan(CompiledSourceBindingPlan, TrailingInit):
        pass

    ExtendedPlan(bindings=[])
    assert events == ["trailing"]
    with pytest.raises(TypeError):
        ExtendedPlan(bindings=Inherit())
    assert events == ["trailing", "trailing"]
    assert "__post_init__" not in CompiledSourceBindingPlan.__dict__
