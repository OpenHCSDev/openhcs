"""Form choice sets for fields that hold axes.

Kept out of :mod:`openhcs.core.axes` so that declaring and activating a family
(done by the product entry point in every process) stays free of the
annotation library. JSON spells a declaration by its registry key, its name.
"""

from __future__ import annotations

from python_introspect import AnnotationChoices

from openhcs.core.axes import AxisFamily


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


__all__ = ["AxisChoices", "GroupingChoices", "VariableAxisChoices"]
