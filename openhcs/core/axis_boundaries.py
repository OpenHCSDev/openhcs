"""Form choice sets and the JSON decoder for fields that hold axes.

Kept out of :mod:`openhcs.core.axes` so that declaring and activating a family
(done by the product entry point in every process) stays free of the
annotation library. JSON spells a declaration by its name, decoded through the
active family.
"""

from __future__ import annotations

from metaclass_registry import AutoRegisterMeta
from python_introspect import AnnotationChoices, registered_class_from_key, to_jsonable

from openhcs.core.axes import AxisDeclarationMeta, AxisFamily, GroupingDeclaration


class _AxisDeclarationChoices(AnnotationChoices):
    def label(self, choice: object) -> str:
        return choice.name  # type: ignore[attr-defined]

    def __eq__(self, other: object) -> bool:
        return type(self) is type(other)

    def __hash__(self) -> int:
        return hash(type(self))

    def __repr__(self) -> str:
        return f"{type(self).__name__}()"


class AxisChoices(_AxisDeclarationChoices):
    """A field holding any axis of the active family."""

    def choices(self) -> tuple[object, ...]:
        return AxisFamily.active().axes


class VariableAxisChoices(_AxisDeclarationChoices):
    """A field holding variable axes of the active family."""

    def choices(self) -> tuple[object, ...]:
        return AxisFamily.active().variable_axes()


class GroupingChoices(_AxisDeclarationChoices):
    """A field holding a grouping declaration of the active family."""

    def choices(self) -> tuple[object, ...]:
        return AxisFamily.active().grouping_choices()



@to_jsonable.register(AxisDeclarationMeta)
def _boundary_name_of_declaration(declaration: AxisDeclarationMeta) -> object:
    """Spell a grouping declaration by its boundary name."""

    if issubclass(declaration, GroupingDeclaration) and "name" in vars(declaration):
        return declaration.name
    return to_jsonable.dispatch(AutoRegisterMeta)(declaration)


@registered_class_from_key.register(AxisDeclarationMeta)
def _declaration_from_boundary_name(family: AxisDeclarationMeta, key: object) -> type:
    """Decode a grouping declaration through the active family.

    Names are unique within a family, not across families, so the active
    family decodes them.
    """

    if issubclass(family, GroupingDeclaration):
        return AxisFamily.active().grouping_named(str(key))
    return registered_class_from_key.dispatch(AutoRegisterMeta)(family, key)


__all__ = ["AxisChoices", "GroupingChoices", "VariableAxisChoices"]
