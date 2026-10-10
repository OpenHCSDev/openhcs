"""The microscopy axis declarations a viewer stream carries, for viewer tests."""

from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.axes import OrdinalValued
from openhcs.runtime.viewer_display import DECLARED_AXES_FIELD, DeclaredAxes, DeclaredAxis

STREAM_AXES = DeclaredAxes.of(Microscopy.axes)


def display_config_mapping(component_modes, component_order, **extra):
    """A display-config wire section declaring the microscopy axes."""

    return {
        "component_modes": dict(component_modes),
        "component_order": list(component_order),
        DECLARED_AXES_FIELD: STREAM_AXES.to_wire(),
        **extra,
    }


def ordinal_axes(*names: str) -> DeclaredAxes:
    """Role-less ordinal axes, for viewer tests that use synthetic axis names."""

    return DeclaredAxes(
        tuple(DeclaredAxis(name, name.title(), (), OrdinalValued) for name in names)
    )
