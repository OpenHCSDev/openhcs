"""
Prototype: Unified None-forcing via make_dataclass()

Goal: ONE path for both base and lazy classes.
Instead of patching Field objects after @dataclass, rebuild the class
with correct defaults from the start.
"""

import dataclasses
from dataclasses import dataclass, field, fields, MISSING, make_dataclass
from typing import Set, Type, Optional
import copy


def get_inherited_field_names(cls: Type) -> Set[str]:
    """Get names of fields inherited from parent classes (not defined in cls itself)."""
    # Fields explicitly defined in this class (in its own __annotations__)
    own_annotations = getattr(cls, "__annotations__", {})
    # But we need to check what's ACTUALLY defined in this class vs inherited

    # Get all field names from parent classes
    parent_fields = set()
    for base in cls.__mro__[1:]:  # Skip cls itself
        if dataclasses.is_dataclass(base):
            parent_fields.update(base.__dataclass_fields__.keys())

    # Fields in this class that are also in parents = inherited (unless redefined)
    # A field is "inherited" if it's in parent_fields but NOT in cls's own __annotations__

    # Get cls's OWN annotations (not inherited)
    own_defined = set()
    if "__annotations__" in cls.__dict__:  # Check cls.__dict__, not getattr
        own_defined = set(cls.__dict__["__annotations__"].keys())

    inherited = parent_fields - own_defined
    return inherited


def rebuild_with_none_defaults(
    cls: Type,
    field_names_to_none: Optional[Set[str]] = None,
    new_name: Optional[str] = None,
) -> Type:
    """
    Rebuild a dataclass via make_dataclass with None defaults for specified fields.

    Args:
        cls: The dataclass to rebuild
        field_names_to_none: Fields that should have default=None.
                            If None, ALL fields get default=None.
        new_name: Optional new class name (for lazy classes)

    Returns:
        A new class with the same fields but modified defaults
    """
    if not dataclasses.is_dataclass(cls):
        raise ValueError(f"{cls} is not a dataclass")

    if field_names_to_none is None:
        # All fields get None (for lazy classes)
        field_names_to_none = {f.name for f in fields(cls)}

    # Build field definitions
    field_defs = []
    for f in fields(cls):
        if f.name in field_names_to_none:
            # Force None default
            field_defs.append(
                (f.name, f.type, field(default=None, metadata=f.metadata))
            )
        else:
            # Preserve original field (copy to avoid sharing)
            field_defs.append((f.name, f.type, copy.copy(f)))

    # Collect non-dunder methods and class attributes to preserve
    namespace = {}
    for key, value in cls.__dict__.items():
        if key.startswith("__") and key.endswith("__"):
            continue  # Skip dunders (make_dataclass will generate them)
        if key == "__dataclass_fields__":
            continue  # Will be regenerated
        namespace[key] = value

    # For bases, we need to keep them for isinstance() to work.
    # make_dataclass with explicit field definitions should override inherited fields.
    bases = cls.__bases__

    # Create new class
    new_cls = make_dataclass(
        new_name or cls.__name__,
        fields=field_defs,
        bases=bases,
        namespace=namespace,
    )

    # Preserve module and qualname
    new_cls.__module__ = cls.__module__
    if new_name is None:
        new_cls.__qualname__ = cls.__qualname__

    return new_cls


# ============ TESTS ============


@dataclass
class Parent:
    x: int = 5
    y: str = "hello"


@dataclass
class Child(Parent):
    z: bool = True  # Explicitly defined in Child


print("=== Original Classes ===")
print(f"Parent fields: {[(f.name, f.default) for f in fields(Parent)]}")
print(f"Child fields:  {[(f.name, f.default) for f in fields(Child)]}")
print(f"Child inherited: {get_inherited_field_names(Child)}")

print("\n=== Rebuild Child with None for inherited fields ===")
NewChild = rebuild_with_none_defaults(Child, get_inherited_field_names(Child))
print(f"NewChild fields: {[(f.name, f.default) for f in fields(NewChild)]}")
print(f"NewChild(): {NewChild()}")
print(f"NewChild(x=10): {NewChild(x=10)}")

print("\n=== Rebuild as Lazy (all fields None) ===")
LazyChild = rebuild_with_none_defaults(Child, None, "LazyChild")
print(f"LazyChild fields: {[(f.name, f.default) for f in fields(LazyChild)]}")
print(f"LazyChild(): {LazyChild()}")

print("\n=== Verify Parent unchanged ===")
print(f"Parent fields: {[(f.name, f.default) for f in fields(Parent)]}")
print(f"Parent(): {Parent()}")

print("\n=== Field object identity ===")
print(f"Parent.x Field id: {id(Parent.__dataclass_fields__['x'])}")
print(f"NewChild.x Field id: {id(NewChild.__dataclass_fields__['x'])}")
print(f"Same? {Parent.__dataclass_fields__['x'] is NewChild.__dataclass_fields__['x']}")

print("\n=== isinstance checks ===")
print(f"isinstance(NewChild(), Parent): {isinstance(NewChild(), Parent)}")
print(f"NewChild.__bases__: {NewChild.__bases__}")
print(f"Child.__bases__: {Child.__bases__}")

# Test with nested dataclass
print("\n=== Nested dataclass test ===")


@dataclass
class NestedConfig:
    value: int = 42


@dataclass
class ParentWithNested:
    nested: NestedConfig = field(default_factory=NestedConfig)
    name: str = "parent"


@dataclass
class ChildWithNested(ParentWithNested):
    extra: bool = True


print(f"ChildWithNested inherited: {get_inherited_field_names(ChildWithNested)}")
NewChildWithNested = rebuild_with_none_defaults(
    ChildWithNested, get_inherited_field_names(ChildWithNested)
)
print(
    f"NewChildWithNested fields: {[(f.name, f.default, f.default_factory) for f in fields(NewChildWithNested)]}"
)
print(f"NewChildWithNested(): {NewChildWithNested()}")
