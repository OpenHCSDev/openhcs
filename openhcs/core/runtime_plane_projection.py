"""Nominal runtime plane projection semantics."""

from __future__ import annotations
from abc import ABC
from abc import abstractmethod
from dataclasses import dataclass
from metaclass_registry import AutoRegisterMeta
from collections.abc import Callable, Sequence
from typing import Any, ClassVar
from typing import Self
from typing import TYPE_CHECKING

from openhcs.core.axes import AxisFamily

if TYPE_CHECKING:
    from openhcs.core.aligned_image_payload import AlignedImageStackKwargResolver
    from openhcs.core.runtime_image_values import ImagePayloadMetadata
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
    def declared_plane_axis(self) -> "type[RuntimePlaneAxis]":
        """Return the leading plane axis this value declares."""
        return NoPlaneAxis

    @property
    def image_metadata(self) -> "ImagePayloadMetadata":
        """Return the image metadata this value carries; only images carry any."""
        from openhcs.core.runtime_image_values import ImagePayloadMetadata

        return ImagePayloadMetadata()

    @property
    def array_data(self) -> object:
        """Return the array a writer stores for this value; only images unwrap."""
        return self

    def scalar_source_provenance(self) -> "SourceImageProvenance":
        """Return the source provenance of this value read as one runtime slice."""
        return self.image_metadata.source_provenance

    def slice_source_provenances(self) -> "tuple[SourceImageProvenance, ...]":
        """Return the source provenance of each runtime slice, without reading pixels."""
        from openhcs.core.axes import ColourAxis

        count = self.runtime_slice_count()
        metadata = self.image_metadata
        provenance = metadata.source_provenance
        if count is None:
            return (provenance,)
        if metadata.axis_position(ColourAxis) == 0:
            raise ValueError(
                "Image metadata cannot declare the same leading axis as both "
                "plane and channel."
            )
        return tuple(provenance.for_source_plane(index) for index in range(count))

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

    def stored_slices(self) -> tuple[object, ...]:
        """Return the separately stored members ``map_slices`` transforms."""
        return (self,)

    def match_alignment(
        self,
        *,
        scalar: Callable[[Any], Any],
        aligned: Callable[[Any], Any],
    ) -> Any:
        """Answer through ``scalar``; values carried one per slice use ``aligned``."""
        del aligned
        return scalar(self)

    def contextualized_output(
        self,
        kind: Any,
        source: object,
        target: Any,
        plane_projection: "RuntimePlaneAxisValueProjection | None",
    ) -> object:
        """Return this returned value contextualized as an output of ``kind``."""
        return kind.contextualize_value(source, self, target, plane_projection)


class RuntimeSliceIndexedValue(RuntimeSliceProjectableValue):
    """A value whose runtime-slice projection selects one slice index."""

    @abstractmethod
    def project_runtime_slice(self, slice_index: int) -> object:
        """Return the value represented by one runtime-slice index."""

    def value_for_slice(self, context: "RuntimePlaneAxisValueProjection") -> object:
        if context.axis.one_plane_per_runtime_slice:
            return self.project_runtime_slice(context.require_plane_index())
        return self

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
        if context.axis.one_plane_per_runtime_slice:
            return self.with_runtime_slice_identity(
                slice_index=context.require_plane_index(),
                slice_count=context.axis_size,
            )
        return self


class RuntimePlaneAxis(ABC, metaclass=AutoRegisterMeta):
    """What the leading plane axis of a runtime array stack counts.

    Each kind of axis is a subclass, used as a class; ``name`` is its spelling
    in viewer messages, saved metadata and error text.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[RuntimePlaneAxis]]] = {}

    name: ClassVar[str | None] = None
    leads_data: ClassVar[bool] = True
    """The data has a leading dimension that counts planes of this axis."""
    unstacked: ClassVar[bool] = False
    """The data has no leading plane dimension (the opposite of ``leads_data``)."""
    one_plane_per_runtime_slice: ClassVar[bool] = False
    """Each plane is one runtime slice of the invocation."""
    one_plane_per_source_binding: ClassVar[bool] = False
    """Each plane is one bound source image."""
    keeps_image_whole: ClassVar[bool] = True
    """An image with this axis can still be one whole image of its spatial domain."""

    @classmethod
    def require_runtime_slices(
        cls, message: str, *, error: type[Exception] = ValueError
    ) -> None:
        """Raise ``error(message)`` unless each plane is one runtime slice."""
        if cls.one_plane_per_runtime_slice:
            return
        raise error(message)

    @classmethod
    def require_source_bindings(cls, message: str) -> None:
        """Raise ``ValueError(message)`` unless each plane is one bound source image."""
        if cls.one_plane_per_source_binding:
            return
        raise ValueError(message)

    @classmethod
    def leading_axes(cls) -> tuple[type[RuntimePlaneAxis], ...]:
        """Return every axis that puts a leading plane dimension on the data."""
        return tuple(axis for axis in cls.__registry__.values() if axis.leads_data)

    @classmethod
    def require_member(cls, value: object) -> type[RuntimePlaneAxis]:
        """Return ``value`` when it is one of this family's axes."""
        if isinstance(value, type) and issubclass(value, RuntimePlaneAxis):
            return value
        raise ValueError(f"{value!r} is not a runtime plane axis.")

    @classmethod
    def named(cls, name: object) -> type[RuntimePlaneAxis]:
        """Return the axis a viewer message or saved record spells as ``name``."""
        try:
            return cls.__registry__[name]
        except (KeyError, TypeError):
            raise ValueError(f"Unknown runtime plane axis {name!r}.") from None

    @classmethod
    @abstractmethod
    def plane_index(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        """Resolve this axis against an execution-local projector."""

    @classmethod
    @abstractmethod
    def axis_size(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        """Resolve this axis cardinality against an execution-local projector."""

    @classmethod
    @abstractmethod
    def projected_axis(cls, projected_plane_count: int) -> type[RuntimePlaneAxis]:
        """Return the axis retained after an exact runtime projection."""

    @classmethod
    def keeps_planes_of(cls, plane_axis: type[RuntimePlaneAxis]) -> bool:
        """Whether composing along this axis keeps a member's existing plane axis."""
        return plane_axis is cls

    @classmethod
    def axis_when_stacked(cls) -> type[RuntimePlaneAxis]:
        """Return the axis that members declaring this axis are stacked along."""
        return cls

    @classmethod
    @abstractmethod
    def compose_provenance(
        cls,
        provenances: "Sequence[SourceImageProvenance]",
        *,
        scalar_sources: "Sequence[SourceImageProvenance]",
        **topology: bool,
    ) -> "SourceImageProvenance":
        """Return the source provenance of members composed along this axis.

        ``topology`` forwards ``preserve_single_topology``; each axis has its
        own default for a single member.
        """


class RuntimeSlicePlaneAxis(RuntimePlaneAxis):
    """One plane per runtime slice; composing along it stacks the slices."""

    name = "runtime_slice"
    one_plane_per_runtime_slice = True

    @classmethod
    def plane_index(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        del source_aliases
        return projector.runtime_slice_plane_index()

    @classmethod
    def axis_size(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        del source_aliases
        return projector.runtime_slice_axis_size()

    @classmethod
    def projected_axis(cls, projected_plane_count: int) -> type[RuntimePlaneAxis]:
        if projected_plane_count != 1:
            raise ValueError(
                "Runtime-slice object-label projection must select exactly one "
                f"plane, got {projected_plane_count}."
            )
        return NoPlaneAxis

    @classmethod
    def keeps_planes_of(cls, plane_axis: type[RuntimePlaneAxis]) -> bool:
        return plane_axis is cls or plane_axis.unstacked

    @classmethod
    def compose_provenance(
        cls,
        provenances: "Sequence[SourceImageProvenance]",
        *,
        scalar_sources: "Sequence[SourceImageProvenance]",
        **topology: bool,
    ) -> "SourceImageProvenance":
        from openhcs.core.source_image_provenance import SourceImageProvenance

        return SourceImageProvenance.stack(
            provenances, scalar_sources=scalar_sources, **topology
        )


class SourceBindingPlaneAxis(RuntimePlaneAxis):
    """One plane per bound source image; composing along it bundles the sources."""

    name = "source_binding"
    one_plane_per_source_binding = True
    keeps_image_whole = False

    @classmethod
    def plane_index(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        return projector.source_binding_axis_plane_index(source_aliases)

    @classmethod
    def axis_size(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        return projector.source_binding_axis_size(source_aliases)

    @classmethod
    def projected_axis(cls, projected_plane_count: int) -> type[RuntimePlaneAxis]:
        if projected_plane_count <= 0:
            raise ValueError(
                "Source-binding object-label projection must select at least one plane."
            )
        if projected_plane_count == 1:
            return NoPlaneAxis
        return cls

    @classmethod
    def compose_provenance(
        cls,
        provenances: "Sequence[SourceImageProvenance]",
        *,
        scalar_sources: "Sequence[SourceImageProvenance]",
        **topology: bool,
    ) -> "SourceImageProvenance":
        from openhcs.core.source_image_provenance import SourceImageProvenance

        return SourceImageProvenance.bundle(
            provenances, scalar_sources=scalar_sources, **topology
        )


class NoPlaneAxis(RuntimePlaneAxis):
    """The data has no leading plane dimension: it is one plane or one whole image."""

    name = "none"
    leads_data = False
    unstacked = True

    @classmethod
    def plane_index(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        del projector, source_aliases
        return None

    @classmethod
    def axis_size(
        cls,
        projector: "RuntimePlaneAxisProjector",
        source_aliases: tuple[str, ...],
    ) -> int | None:
        del projector, source_aliases
        return None

    @classmethod
    def projected_axis(cls, projected_plane_count: int) -> type[RuntimePlaneAxis]:
        raise ValueError("Data without a plane axis has no planes to project.")

    @classmethod
    def keeps_planes_of(cls, plane_axis: type[RuntimePlaneAxis]) -> bool:
        del plane_axis
        return False

    @classmethod
    def axis_when_stacked(cls) -> type[RuntimePlaneAxis]:
        return RuntimeSlicePlaneAxis

    @classmethod
    def compose_provenance(
        cls,
        provenances: "Sequence[SourceImageProvenance]",
        *,
        scalar_sources: "Sequence[SourceImageProvenance]",
        **topology: bool,
    ) -> "SourceImageProvenance":
        raise ValueError("Members are composed along a declared plane axis.")


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
class RuntimePlaneProjection(RuntimePlaneAxisProjector, ABC):
    """Which planes of a runtime stack an execution scope works on.

    ``WholeStackProjection`` keeps the stack; ``StackPlaneSelection`` selects
    one explicitly proven plane.
    """

    plane_count: int | None = None

    selects_one_plane: ClassVar[bool]

    def __post_init__(self) -> None:
        if self.plane_count is None:
            return
        plane_count = int(self.plane_count)
        if plane_count <= 0:
            raise ValueError("Runtime-plane projection plane_count must be positive.")
        object.__setattr__(self, "plane_count", plane_count)

    @staticmethod
    def stack(plane_count: int | None = None) -> "WholeStackProjection":
        """Preserve runtime-slice stacks for stack-scoped execution."""
        return WholeStackProjection(plane_count=plane_count)

    @staticmethod
    def selected(
        plane_index: int, plane_count: int | None = None
    ) -> "StackPlaneSelection":
        """Select one runtime-slice plane from an explicit projection proof."""
        return StackPlaneSelection(plane_count=plane_count, plane_index=plane_index)

    @property
    def preserves_complete_axis(self) -> bool:
        """Whether this projection keeps every plane instead of selecting one."""
        return not self.selects_one_plane

    def runtime_slice_axis_size(self) -> int | None:
        """Return the grouped runtime-slice axis size when known."""
        return self.plane_count


@dataclass(frozen=True, slots=True)
class WholeStackProjection(RuntimePlaneProjection):
    """Keep every plane of the runtime stack."""

    selects_one_plane = False

    def runtime_slice_plane_index(self) -> None:
        return None


@dataclass(frozen=True, slots=True, kw_only=True)
class StackPlaneSelection(RuntimePlaneProjection):
    """Select one plane of the runtime stack."""

    plane_index: int

    selects_one_plane = True

    def __post_init__(self) -> None:
        RuntimePlaneProjection.__post_init__(self)
        plane_index = int(self.plane_index)
        if plane_index < 0:
            raise ValueError("Runtime-plane projection plane_index cannot be negative.")
        if self.plane_count is not None and plane_index >= self.plane_count:
            raise ValueError(
                "Runtime-plane projection plane_index must be within plane_count: "
                f"index {plane_index}, count {self.plane_count}."
            )
        object.__setattr__(self, "plane_index", plane_index)

    def runtime_slice_plane_index(self) -> int:
        return self.plane_index


@dataclass(frozen=True, slots=True)
class RuntimePlaneAxisValueProjection(RuntimeSliceIndexedValue, ABC):
    """Projection of values that explicitly carry a declared runtime plane axis.

    ``WholeAxisProjection`` keeps every plane of the axis;
    ``SelectedPlaneProjection`` selects one.
    """

    axis: type[RuntimePlaneAxis]
    source_aliases: tuple[str, ...]
    axis_size: int

    preserves_complete_axis: ClassVar[bool]
    """Whether this projection keeps every plane instead of selecting one."""

    def __post_init__(self) -> None:
        axis = RuntimePlaneAxis.require_member(self.axis)
        if axis.unstacked:
            raise ValueError(
                "RuntimePlaneAxisValueProjection requires an axis that leads the data."
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
        object.__setattr__(self, "axis", axis)
        object.__setattr__(self, "source_aliases", source_aliases)
        object.__setattr__(self, "axis_size", axis_size)

    @property
    def selects_one_plane(self) -> bool:
        """Whether this projection selects one plane of its axis."""
        return not self.preserves_complete_axis

    @abstractmethod
    def selected_planes(self) -> tuple[int, ...]:
        """Return the plane indices of the axis this projection keeps."""

    def selects_same_planes(self, other: "RuntimePlaneAxisValueProjection") -> bool:
        """Whether ``other`` keeps or selects the same planes the same way."""
        return (
            self.preserves_complete_axis == other.preserves_complete_axis
            and self.selected_planes() == other.selected_planes()
        )

    @staticmethod
    def for_plane(
        *,
        axis: type[RuntimePlaneAxis],
        plane_index: int | None,
        axis_size: int,
        source_aliases: tuple[str, ...] = (),
    ) -> "RuntimePlaneAxisValueProjection":
        """Build from a resolver's answer: an index selects, ``None`` keeps the axis."""
        if plane_index is None:
            return WholeAxisProjection(axis, tuple(source_aliases), axis_size)
        return SelectedPlaneProjection(
            axis, tuple(source_aliases), axis_size, plane_index
        )

    @classmethod
    def from_source_declaration(
        cls,
        axis: type[RuntimePlaneAxis],
        source: "SourceImageProvenance",
    ) -> "RuntimePlaneAxisValueProjection | None":
        """Construct the retained axis declared by an exact source-image value.

        A missing axis declares no plane projection, even when provenance has
        multiple contributors. Cardinality and aliases come from that source
        source declaration; array rank never supplies spatial meaning.
        """
        if axis.unstacked:
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
        axis: type[RuntimePlaneAxis],
        source_aliases: tuple[str, ...],
    ) -> "RuntimePlaneAxisValueProjection | None":
        """Return the runtime-axis projection declared by a runtime projector."""
        if projector is None:
            return None
        if not isinstance(projector, RuntimePlaneAxisProjector):
            raise TypeError(
                f"Runtime plane-axis projection requires RuntimePlaneAxisProjector, got {type(projector).__name__}."
            )
        source_aliases = tuple(source_aliases)
        axis_size = axis.axis_size(projector, source_aliases)
        if axis_size is None:
            return None
        return cls.for_plane(
            axis=axis,
            source_aliases=source_aliases,
            plane_index=axis.plane_index(projector, source_aliases),
            axis_size=axis_size,
        )

    def validate_source_declaration(
        self, axis: type[RuntimePlaneAxis], source: "SourceImageProvenance",
    ) -> None:
        """Check an explicit projection against retained acquisition declarations."""
        if axis.unstacked:
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
        axis: type[RuntimePlaneAxis],
        source_aliases: tuple[str, ...] = (),
    ) -> "RuntimePlaneAxisValueProjection":
        """Return the complete projection declared for one runtime image axis."""

        projection = cls.from_projector(projector, axis, source_aliases)
        if projection is None:
            raise ValueError(
                f"Declared {axis.name!r} image axis has no runtime cardinality."
            )
        return projection

    @classmethod
    def from_selected_plane(
        cls,
        *,
        axis: type[RuntimePlaneAxis],
        plane_index: int,
        axis_size: int,
        source_aliases: tuple[str, ...] = (),
    ) -> "RuntimePlaneAxisValueProjection":
        """Return a projection whose explicit plane proof is already resolved."""
        return SelectedPlaneProjection(
            axis, tuple(source_aliases), axis_size, plane_index
        )

    @classmethod
    def preserve(
        cls,
        *,
        axis: type[RuntimePlaneAxis],
        axis_size: int,
        source_aliases: tuple[str, ...] = (),
    ) -> "RuntimePlaneAxisValueProjection":
        """Declare a complete runtime axis without selecting one plane."""

        return WholeAxisProjection(axis, tuple(source_aliases), axis_size)

    def selected_plane(self, plane_index: int) -> "RuntimePlaneAxisValueProjection":
        """Select one plane while preserving this declaration's exact axis."""

        return self.from_selected_plane(
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

    @staticmethod
    def require_axis_size(
        projection: "RuntimePlaneAxisValueProjection | None",
        slice_count: int,
        *,
        value_name: str,
    ) -> "RuntimePlaneAxisValueProjection":
        """Require a declared projection whose axis carries ``slice_count`` planes."""
        if projection is None or projection.axis_size != slice_count:
            raise ValueError(
                f"{value_name} require an exact source plane projection of "
                f"{slice_count} plane(s)."
            )
        return projection

    @staticmethod
    def require_runtime_slice_projection(
        projection: "RuntimePlaneAxisValueProjection | None", message: str
    ) -> "RuntimePlaneAxisValueProjection":
        """Return ``projection`` when it is declared on the runtime-slice axis."""
        if projection is None:
            raise ValueError(message)
        projection.axis.require_runtime_slices(message)
        return projection

    @staticmethod
    def require_runtime_slice_axis(
        projection: "RuntimePlaneAxisValueProjection | None",
        slice_count: int,
        *,
        value_name: str,
    ) -> "RuntimePlaneAxisValueProjection":
        """Require the runtime-slice axis, declared with ``slice_count`` planes."""
        projection = RuntimePlaneAxisValueProjection.require_runtime_slice_projection(
            projection, f"{value_name} requires an exact runtime slice projection."
        )
        if projection.axis_size != slice_count:
            raise ValueError(
                f"{value_name} count must exactly match the declared runtime plane "
                f"axis: {slice_count} != {projection.axis_size}."
            )
        return projection

    @abstractmethod
    def require_plane_index(self) -> int:
        """Return the selected plane index required by a projected invocation."""

    @abstractmethod
    def require_complete_axis(self, *, value_name: str) -> Self:
        """Require that this declaration preserves every input plane."""

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
                f"{value_name} does not match its declared {self.axis.name!r} "
                f"axis of size {self.axis_size}: shape {shape!r}."
            )

    @staticmethod
    def validate_plane_index(plane_index: int, shape: tuple[int, ...]) -> None:
        """Validate a selected source-binding plane against dense data shape."""
        if plane_index < 0 or plane_index >= shape[0]:
            raise RuntimeError(
                f"Runtime plane-axis projection produced an out-of-range plane index {plane_index} for shape {shape!r}."
            )


@dataclass(frozen=True, slots=True)
class WholeAxisProjection(RuntimePlaneAxisValueProjection):
    """Keep every plane of the declared axis."""

    preserves_complete_axis = True

    @classmethod
    def preserve(
        cls,
        *,
        axis: type[RuntimePlaneAxis],
        axis_size: int,
        source_aliases: tuple[str, ...] = (),
    ) -> Self:
        return cls(axis, tuple(source_aliases), axis_size)

    def selected_planes(self) -> tuple[int, ...]:
        return tuple(range(self.axis_size))

    def require_plane_index(self) -> int:
        raise ValueError(
            "Runtime plane projection requires an explicitly selected plane."
        )

    def require_complete_axis(self, *, value_name: str) -> Self:
        del value_name
        return self


@dataclass(frozen=True, slots=True)
class SelectedPlaneProjection(RuntimePlaneAxisValueProjection):
    """Select one plane of the declared axis."""

    plane_index: int

    preserves_complete_axis = False

    def __post_init__(self) -> None:
        RuntimePlaneAxisValueProjection.__post_init__(self)
        plane_index = int(self.plane_index)
        if plane_index < 0 or plane_index >= self.axis_size:
            raise ValueError(
                "RuntimePlaneAxisValueProjection.plane_index must be within "
                f"axis_size: index {plane_index}, size {self.axis_size}."
            )
        object.__setattr__(self, "plane_index", plane_index)

    def selected_planes(self) -> tuple[int, ...]:
        return (self.plane_index,)

    def require_plane_index(self) -> int:
        return self.plane_index

    def require_complete_axis(self, *, value_name: str) -> Self:
        raise ValueError(f"{value_name} requires a complete input stack projection.")
