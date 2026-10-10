"""One nominal class per streaming viewer.

A :class:`ViewerFamily` leaf declares everything that differs between
viewers: its wire name, storage backend, display settings (and through them
its slot family), and its lifecycle implementation. Config keys, titles and
step-plan keys are derived from the wire name. ``ViewerType`` is the boundary
view of the registry for wire and form fields.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from enum import Enum
from typing import TYPE_CHECKING, ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.constants.constants import Backend
from openhcs.runtime.viewer_display import (
    FijiDisplaySettings,
    NapariDisplaySettings,
    ViewerDisplaySettings,
)

if TYPE_CHECKING:
    from polystore.filemanager import FileManager

    from openhcs.core.execution_visualizer import ExecutionVisualizerABC
    from openhcs.core.streaming_config_factory import StreamingViewerRuntimeConfig


class ViewerFamily(ABC, metaclass=AutoRegisterMeta):
    """One streaming viewer; leaves register by their wire name."""

    __registry_key__ = "wire_value"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["ViewerFamily"]]]

    wire_value: ClassVar[str | None] = None
    backend: ClassVar[Backend]
    display_settings: ClassVar[type[ViewerDisplaySettings]]

    display_name: ClassVar[str]
    config_key: ClassVar[str]
    step_plan_output_key: ClassVar[str]
    title: ClassVar[str]

    def __init_subclass__(cls, **kwargs: object) -> None:
        super().__init_subclass__(**kwargs)
        if cls.__dict__.get("wire_value") is None:
            return
        cls.display_name = cls.__name__.removesuffix("Viewer")
        cls.config_key = f"{cls.wire_value}_streaming_config"
        cls.step_plan_output_key = f"{cls.wire_value}_streaming_paths"
        cls.title = f"OpenHCS {cls.display_name} Visualization"

    def __new__(cls, *args: object, **kwargs: object):
        raise TypeError(f"{cls.__qualname__} is a viewer declaration, not a value type.")

    @classmethod
    @abstractmethod
    def visualizer_type(cls) -> type["ExecutionVisualizerABC"]:
        """Load this viewer's lifecycle implementation."""

    @classmethod
    def create_visualizer(
        cls,
        *,
        filemanager: "FileManager",
        runtime_config: "StreamingViewerRuntimeConfig",
    ) -> "ExecutionVisualizerABC":
        return cls.visualizer_type()(
            filemanager=filemanager,
            runtime_config=runtime_config,
        )

    @classmethod
    def families(cls) -> tuple[type["ViewerFamily"], ...]:
        return tuple(ViewerFamily.__registry__.values())

    @classmethod
    def named(cls, wire_value: object) -> type["ViewerFamily"]:
        """Decode one viewer wire name (a ``ViewerType`` member or its value)."""

        key = wire_value.value if isinstance(wire_value, Enum) else wire_value
        if key not in ViewerFamily.__registry__:
            raise ValueError(
                f"Unknown viewer {wire_value!r}; viewers are "
                f"{sorted(ViewerFamily.__registry__)!r}."
            )
        return ViewerFamily.__registry__[key]

    @classmethod
    def for_config_key(cls, config_key: str) -> type["ViewerFamily"]:
        """Decode an ObjectState streaming-config field key."""

        for family in cls.families():
            if family.config_key == config_key:
                return family
        raise ValueError(f"Unknown viewer streaming config key: {config_key!r}")

    @classmethod
    def viewer_type(cls) -> "ViewerType":
        """This viewer's boundary enum member."""

        return ViewerType(cls.wire_value)


class NapariViewer(ViewerFamily):
    wire_value = "napari"
    backend = Backend.NAPARI_STREAM
    display_settings = NapariDisplaySettings

    @classmethod
    def visualizer_type(cls) -> type["ExecutionVisualizerABC"]:
        from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer

        return NapariStreamVisualizer


class FijiViewer(ViewerFamily):
    wire_value = "fiji"
    backend = Backend.FIJI_STREAM
    display_settings = FijiDisplaySettings

    @classmethod
    def visualizer_type(cls) -> type["ExecutionVisualizerABC"]:
        from openhcs.runtime.fiji_stream_visualizer import FijiStreamVisualizer

        return FijiStreamVisualizer


ViewerType = Enum(
    "ViewerType",
    [
        (family.display_name.upper(), family.wire_value)
        for family in sorted(ViewerFamily.families(), key=lambda family: family.wire_value)
    ],
    module=__name__,
)
"""Boundary view of the viewer registry, for wire fields and form choices."""
ViewerType.__doc__ = "Streaming viewer names at wire and form boundaries."
ViewerType.family = property(lambda member: ViewerFamily.named(member.value))
