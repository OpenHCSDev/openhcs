"""Nominal runtime plane projection semantics."""

from __future__ import annotations
from abc import ABC
from abc import abstractmethod
from dataclasses import dataclass
from enum import Enum
from metaclass_registry import AutoRegisterMeta
from metaclass_registry.strategies import EnumKeyedStrategyMixin
from collections.abc import Callable, Sequence
from typing import Any, ClassVar
from typing import Self
from typing import TYPE_CHECKING

from openhcs.core.axes import AxisFamily

if TYPE_CHECKING:
    from openhcs.core.aligned_image_payload import AlignedImageStackKwargResolver
    from openhcs.core.source_image_provenance import SourceImageProvenance


class RuntimeSliceProjectableValue(ABC):
    """A runtime value that owns how it splits into runtime slices.

    Every owned runtime value family joins this ABC; ``RuntimeSliceProjection``
    only handles foreign values (arrays, containers, primitives) itself.
    """

    def runtime_slice_count(self) -> int | None:
        """Return the declared runtime-slice count, or None without that axis."""
        return None

    @property
    def declared_plane_axis(self) -> "RuntimePlaneAxis | None":
        """Return the leading plane axis this value declares, if any."""
        return None

    @abstractmethod
    def value_for_slice(
        self, context: "RuntimePlaneAxisValueProjection"
    ) -> object:
        """Return the value for one selected plane of ``context``'s axis."""

    def identity_projected_value(
        self, context: "RuntimePlaneAxisValueProjection"
    ) -> object:
        """Return the value stamped with one execution slice's identity."""
        del context
        return self

    def full_stack_value(self) -> object:
        """Return the value a whole-stack callable receives."""
        return self

    def aligned_value(self, resolver: "AlignedImageStackKwargResolver") -> object:
        """Return the value bound beside one slice of an aligned image stack."""
        del resolver
        return self

    def alignment_slices(self) -> tuple[object, ...]:
        """Return this value split into the slices of an aligned invocation."""
        return (self,)

    def output_slices(self) -> tuple[object, ...]:
        """Return the scalar values this value publishes as outputs."""
        return self.alignment_slices()

    def map_slices(self, transform: Callable[[Any], Any]) -> Any:
        """Apply ``transform`` to each separately stored member, keeping alignment.

        A value without separately stored members is transformed as a whole.
        """
        return transform(self)


class RuntimeSliceIndexedValue(RuntimeSliceProjectableValue):
    """A value whose runtime-slice projection selects one slice index."""

    @abstractmethod
    def project_runtime_slice(self, slice_index: int) -> object:
        """Return the value represented by one runtime-slice index."""

    def value_for_slice(self, context: "RuntimePlaneAxisValueProjection") -> object:
        if context.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            return self
        return self.project_runtime_slice(context.require_plane_index())

    def aligned_value(self, resolver: "AlignedImageStackKwargResolver") -> object:
        return self.value_for_slice(resolver.projection_axis)


class RuntimeSliceInvariantValue(RuntimeSliceProjectableValue):
    """A value unchanged by runtime-slice projection."""

    def value_for_slice(self, context: "RuntimePlaneAxisValueProjection") -> Self:
        del context
        return self


class RuntimeSliceIdentityProjectableValue(RuntimeSliceProjectableValue):
    """A value that is stamped with the execution slice it was produced in."""

    @abstractmethod
    def with_runtime_slice_identity(
        self, *, slice_index: int, slice_count: int
    ) -> Self:
        """Return the value with execution-slice identity applied."""

    def value_for_slice(self, context: "RuntimePlaneAxisValueProjection") -> object:
        del context
        return self

    def identity_projected_value(
        self, context: "RuntimePlaneAxisValueProjection"
    ) -> object:
        if context.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            return self
        return self.with_runtime_slice_identity(
            slice_index=context.require_plane_index(),
            slice_count=context.axis_size,
        )


class RuntimePlaneAxis(str, Enum):
    """Semantic meaning of the leading plane axis on runtime array stacks."""

    RUNTIME_SLICE = "runtime_slice"
    SOURCE_BINDING = "source_binding"


class RuntimePlaneAxisStrategy(
    EnumKeyedStrategyMixin[RuntimePlaneAxis], ABC, metaclass=AutoRegisterMeta
):
    """Own all behavior for one nominal runtime plane axis."""

    __enum_member_attr__ = "axis"
    axis: ClassVar[RuntimePlaneAxis]
    strategy_label: ClassVar[str | None] = None

    @abstractmethod
    def plane_index(
        self,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        """Resolve this axis against an execution-local projector."""

    @abstractmethod
    def axis_size(
        self,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        """Resolve this axis cardinality against an execution-local projector."""

    @abstractmethod
    def projected_axis(self, projected_plane_count: int) -> RuntimePlaneAxis | None:
        """Return the axis retained after an exact runtime projection."""


class RuntimeSlicePlaneAxisStrategy(RuntimePlaneAxisStrategy):
    """Runtime-slice axis behavior."""

    axis = RuntimePlaneAxis.RUNTIME_SLICE

    def plane_index(
        self,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        del source_aliases
        return projector.runtime_slice_plane_index()

    def axis_size(
        self,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        del source_aliases
        return projector.runtime_slice_axis_size()

    def projected_axis(self, projected_plane_count: int) -> RuntimePlaneAxis | None:
        if projected_plane_count != 1:
            raise ValueError(
                "Runtime-slice object-label projection must select exactly one "
                f"plane, got {projected_plane_count}."
            )
        return None


class SourceBindingPlaneAxisStrategy(RuntimePlaneAxisStrategy):
    """Source-binding axis behavior."""

    axis = RuntimePlaneAxis.SOURCE_BINDING

    def plane_index(
        self,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        return projector.source_binding_axis_plane_index(source_aliases)

    def axis_size(
        self,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        return projector.source_binding_axis_size(source_aliases)

    def projected_axis(self, projected_plane_count: int) -> RuntimePlaneAxis | None:
        if projected_plane_count <= 0:
            raise ValueError(
                "Source-binding object-label projection must select at least one plane."
            )
        if projected_plane_count == 1:
            return None
        return RuntimePlaneAxis.SOURCE_BINDING


class RuntimePlaneAxisProjector(ABC):
    """Nominal provider for execution-local runtime plane selection."""

    @abstractmethod
    def runtime_slice_plane_index(self) -> int | None:
        """Return the execution-local runtime-slice plane index."""

    def runtime_slice_axis_size(self) -> int | None:
        """Return the runtime-slice axis size for the current execution scope."""
        return None

    def source_binding_axis_plane_index(
        self, source_aliases: tuple[str, ...]
    ) -> int | None:
        """Return the execution-local source-binding plane index."""
        raise NotImplementedError(
            f"{type(self).__name__} does not provide source-binding plane projection."
        )

    def source_binding_axis_size(self, source_aliases: tuple[str, ...]) -> int | None:
        """Return the source-binding axis size for this execution scope."""
        return None


@dataclass(frozen=True, slots=True)
class RuntimePlaneProjection(RuntimePlaneAxisProjector):
    """Preserve a runtime stack or select one explicitly proven plane."""

    plane_index: int | None = None
    plane_count: int | None = None

    def __post_init__(self) -> None:
        if self.plane_count is None:
            plane_count = None
        else:
            plane_count = int(self.plane_count)
            if plane_count <= 0:
                raise ValueError(
                    "Runtime-plane projection plane_count must be positive."
                )
            object.__setattr__(self, "plane_count", plane_count)
        if self.plane_index is None:
            return
        plane_index = int(self.plane_index)
        if plane_index < 0:
            raise ValueError("Runtime-plane projection plane_index cannot be negative.")
        if plane_count is not None and plane_index >= plane_count:
            raise ValueError(
                "Runtime-plane projection plane_index must be within plane_count: "
                f"index {plane_index}, count {plane_count}."
            )
        object.__setattr__(self, "plane_index", plane_index)

    @classmethod
    def stack(cls, plane_count: int | None = None) -> "RuntimePlaneProjection":
        """Preserve runtime-slice stacks for stack-scoped execution."""
        return cls(plane_count=plane_count)

    @classmethod
    def selected(
        cls, plane_index: int, plane_count: int | None = None
    ) -> "RuntimePlaneProjection":
        """Select one runtime-slice plane from an explicit projection proof."""
        return cls(plane_index=plane_index, plane_count=plane_count)

    def runtime_slice_plane_index(self) -> int | None:
        """Return selected runtime-slice plane, or None when stacks are preserved."""
        return self.plane_index

    def runtime_slice_axis_size(self) -> int | None:
        """Return the grouped runtime-slice axis size when known."""
        return self.plane_count


@dataclass(frozen=True, slots=True)
class RuntimePlaneAxisValueProjection(RuntimeSliceIndexedValue):
    """Projection of values that explicitly carry a declared runtime plane axis."""

    axis: RuntimePlaneAxis
    source_aliases: tuple[str, ...]
    plane_index: int | None
    axis_size: int

    def __post_init__(self) -> None:
        axis = RuntimePlaneAxis(
            self.axis,
        )
        source_aliases = tuple(self.source_aliases)
        if any(not isinstance(alias, str) or not alias for alias in source_aliases):
            raise ValueError(
                "RuntimePlaneAxisValueProjection.source_aliases must contain "
                "non-empty strings."
            )
        axis_size = int(self.axis_size)
        if axis_size <= 0:
            raise ValueError(
                "RuntimePlaneAxisValueProjection.axis_size must be positive."
            )
        plane_index = self.plane_index
        if plane_index is not None:
            plane_index = int(plane_index)
            if plane_index < 0 or plane_index >= axis_size:
                raise ValueError(
                    "RuntimePlaneAxisValueProjection.plane_index must be within "
                    f"axis_size: index {plane_index}, size {axis_size}."
                )
        object.__setattr__(self, "axis", axis)
        object.__setattr__(self, "source_aliases", source_aliases)
        object.__setattr__(self, "axis_size", axis_size)
        object.__setattr__(self, "plane_index", plane_index)

    @classmethod
    def from_source_declaration(
        cls,
        axis: RuntimePlaneAxis | None,
        source: "SourceImageProvenance",
    ) -> "RuntimePlaneAxisValueProjection | None":
        """Construct the retained axis declared by an exact source-image value.

        A missing axis declares no plane projection, even when provenance has
        multiple contributors. Cardinality and aliases come from that source
        source declaration; array rank never supplies spatial meaning.
        """
        if axis is None:
            return None
        return cls.preserve(
            axis=axis,
            axis_size=source.source_plane_count,
            source_aliases=source.source_image_names,
        )

    @classmethod
    def from_projector(
        cls,
        projector: RuntimePlaneAxisProjector | None,
        axis: RuntimePlaneAxis,
        source_aliases: tuple[str, ...],
    ) -> "RuntimePlaneAxisValueProjection | None":
        """Return the runtime-axis projection declared by a runtime projector."""
        if projector is None:
            return None
        if not isinstance(projector, RuntimePlaneAxisProjector):
            raise TypeError(
                f"Runtime plane-axis projection requires RuntimePlaneAxisProjector, got {type(projector).__name__}."
            )
        axis = RuntimePlaneAxis(axis)
        source_aliases = tuple(source_aliases)
        strategy = RuntimePlaneAxisStrategy.for_enum_member(axis)
        axis_size = strategy.axis_size(projector, source_aliases)
        if axis_size is None:
            return None
        return cls(
            axis=axis,
            source_aliases=source_aliases,
            plane_index=strategy.plane_index(projector, source_aliases),
            axis_size=axis_size,
        )

    def validate_source_declaration(
        self, axis: RuntimePlaneAxis | None, source: "SourceImageProvenance",
    ) -> None:
        """Check an explicit projection against retained acquisition declarations."""
        if axis is None:
            return
        declared_count = source.source_plane_count
        if self.axis is not axis or (
            declared_count > 0 and self.axis_size != declared_count
        ):
            raise ValueError(
                "Object-label plane projection conflicts with the source-image "
                "axis declaration."
            )

    @classmethod
    def require_from_projector(
        cls,
        projector: RuntimePlaneAxisProjector,
        axis: RuntimePlaneAxis,
        source_aliases: tuple[str, ...] = (),
    ) -> "RuntimePlaneAxisValueProjection":
        """Return the complete projection declared for one runtime image axis."""

        projection = cls.from_projector(projector, axis, source_aliases)
        if projection is None:
            raise ValueError(
                f"Declared {axis.value!r} image axis has no runtime cardinality."
            )
        return projection

    @classmethod
    def from_selected_plane(
        cls,
        *,
        axis: RuntimePlaneAxis,
        plane_index: int,
        axis_size: int,
        source_aliases: tuple[str, ...] = (),
    ) -> "RuntimePlaneAxisValueProjection":
        """Return a projection whose explicit plane proof is already resolved."""
        return cls(
            axis=axis,
            source_aliases=tuple(source_aliases),
            plane_index=plane_index,
            axis_size=axis_size,
        )

    @classmethod
    def preserve(
        cls,
        *,
        axis: RuntimePlaneAxis,
        axis_size: int,
        source_aliases: tuple[str, ...] = (),
    ) -> "RuntimePlaneAxisValueProjection":
        """Declare a complete runtime axis without selecting one plane."""

        return cls(
            axis=axis,
            source_aliases=tuple(source_aliases),
            plane_index=None,
            axis_size=axis_size,
        )

    def selected_plane(self, plane_index: int) -> "RuntimePlaneAxisValueProjection":
        """Select one plane while preserving this declaration's exact axis."""

        return type(self).from_selected_plane(
            axis=self.axis,
            source_aliases=self.source_aliases,
            plane_index=plane_index,
            axis_size=self.axis_size,
        )

    def project_runtime_slice(
        self, slice_index: int
    ) -> "RuntimePlaneAxisValueProjection":
        """Select the projection carried into one runtime-slice invocation."""
        return self.selected_plane(slice_index)

    def require_plane_index(self) -> int:
        """Return the selected plane index required by a projected invocation."""

        if self.plane_index is None:
            raise ValueError(
                "Runtime plane projection requires an explicitly selected plane."
            )
        return self.plane_index

    def require_complete_axis(self, *, value_name: str) -> Self:
        """Require that this declaration preserves every input plane."""

        if self.plane_index is not None:
            raise ValueError(f"{value_name} requires a complete input stack projection.")
        return self

    @classmethod
    def require_complete_projection(
        cls,
        projection: RuntimePlaneAxisValueProjection | None,
        *,
        value_name: str,
    ) -> RuntimePlaneAxisValueProjection:
        """Require an optional invocation projection to be a complete input axis."""

        if projection is None:
            raise ValueError(f"{value_name} requires a complete input stack projection.")
        return projection.require_complete_axis(value_name=value_name)

    def dense_shape_carries_axis(self, shape: Sequence[int]) -> bool:
        """Return whether a dense shape carries this declared leading axis."""

        shape = tuple(int(size) for size in shape)
        spatial_rank = AxisFamily.active().payload_spatial_rank
        return len(shape) > spatial_rank and shape[0] == self.axis_size

    def validate_shape(self, shape: Sequence[int], *, value_name: str) -> None:
        """Validate a dense shape against this declared runtime axis."""
        shape = tuple(int(size) for size in shape)
        if not self.dense_shape_carries_axis(shape):
            raise ValueError(
                f"{value_name} does not match its declared {self.axis.value!r} "
                f"axis of size {self.axis_size}: shape {shape!r}."
            )

    @staticmethod
    def validate_plane_index(plane_index: int, shape: tuple[int, ...]) -> None:
        """Validate a selected source-binding plane against dense data shape."""
        if plane_index < 0 or plane_index >= shape[0]:
            raise RuntimeError(
                f"Runtime plane-axis projection produced an out-of-range plane index {plane_index} for shape {shape!r}."
            )
