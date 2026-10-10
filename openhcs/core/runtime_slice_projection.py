"""Nominal runtime-slice projection contracts."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum
from typing import TYPE_CHECKING, Any, TypeAlias, overload

import numpy as np
import numpy.typing as npt
from arraybridge.decorators import DtypeConversionConfig

from openhcs.core.axes import Axis
from openhcs.core.runtime_array_values import RuntimeArrayData, is_array_payload
from openhcs.core.runtime_image_values import ImagePayload, ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
    RuntimeSliceProjectableValue,
)
from openhcs.core.source_image_provenance import SourceComponentMetadata

if TYPE_CHECKING:
    from openhcs.core.aligned_image_payload import AlignedImageStackKwargResolver
    from openhcs.core.runtime_object_labels import ObjectLabelValue

RuntimeProjectionPrimitive: TypeAlias = str | bytes | int | float | bool | None
RuntimeProjectionMapping: TypeAlias = Mapping[str, "RuntimeProjectionData"]
RuntimeProjectionSequence: TypeAlias = Sequence["RuntimeProjectionData"]
RuntimeProjectionDType: TypeAlias = npt.DTypeLike
RuntimeProjectionData: TypeAlias = (
    RuntimeArrayData
    | RuntimeSliceProjectableValue
    | DtypeConversionConfig
    | RuntimeProjectionPrimitive
    | Enum
    | RuntimeProjectionMapping
    | RuntimeProjectionSequence
)


class RuntimeSliceProjectionDeclarationError(ValueError):
    """Raised when runtime-slice behavior has no complete nominal declaration."""


@dataclass(frozen=True, slots=True)
class RuntimeProjectionSourceIdentityRequest:
    """Nominal request for runtime-slice projection with source identity rules."""

    value: RuntimeProjectionData
    source_description: str
    variable_components: Sequence[type[Axis]] = field(default_factory=tuple)
    plane_projection: RuntimePlaneAxisValueProjection | None = None

    def runtime_slice_count(self) -> int | None:
        """Return a count only when a nominal declaration selects stack semantics."""
        if self.plane_projection is not None:
            return self.plane_projection.axis_size
        declared_count = RuntimeSliceProjection.slice_count_from_values((self.value,))
        if declared_count is not None:
            return declared_count
        if not self.variable_components:
            return None
        raise RuntimeSliceProjectionDeclarationError(
            "Variable-component runtime projection requires a nominal payload "
            "with RuntimePlaneAxis.RUNTIME_SLICE; source provenance and ndarray "
            "shape cannot declare the runtime axis."
        )

    def projected_value(
        self, context: RuntimePlaneAxisValueProjection
    ) -> RuntimeProjectionData:
        """Project only through the axis declared by this request."""
        return RuntimeSliceProjection.value_for_slice(self.value, context)

    def source_plane_indices(
        self,
        context: RuntimePlaneAxisValueProjection,
    ) -> tuple[int, ...] | None:
        """Return exact provenance projection for the request-declared stack axis."""
        source_plane_count = self.value.metadata.source_provenance.source_plane_count
        if source_plane_count == 0:
            return None
        if source_plane_count != context.axis_size:
            raise ValueError(
                "Runtime stack source provenance must exactly match the declared "
                f"variable-component axis: {source_plane_count} != {context.axis_size}."
            )
        return (context.require_plane_index(),)

    def plane_metadata(
        self,
        context: RuntimePlaneAxisValueProjection,
    ) -> "RuntimeProjectionPlaneMetadata | None":
        """Return plane identity derived from this request's declared axis."""
        return RuntimeProjectionPlaneMetadata(
            plane_indices=(context.require_plane_index(),),
            plane_shape=(context.axis_size,),
            source_plane_indices=self.source_plane_indices(context) or (),
        )

    def slice_description(self, slice_index: int) -> str:
        """Return the diagnostic description for one projected runtime slice."""
        return f"{self.source_description} runtime slice {slice_index}"


@dataclass(frozen=True, slots=True)
class RuntimeProjectionPlaneMetadata:
    """Plane identity carried by one runtime-slice-projected payload item."""

    plane_indices: tuple[int, ...]
    plane_shape: tuple[int, ...]
    source_plane_indices: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        if not self.plane_indices:
            raise ValueError(
                "RuntimeProjectionPlaneMetadata.plane_indices cannot be empty."
            )
        if len(self.plane_indices) != len(self.plane_shape):
            raise ValueError(
                "RuntimeProjectionPlaneMetadata plane index rank must match "
                "plane shape rank."
            )
        if any(index < 0 for index in self.plane_indices):
            raise ValueError(
                "RuntimeProjectionPlaneMetadata.plane_indices cannot be negative."
            )
        if any(size <= 0 for size in self.plane_shape):
            raise ValueError(
                "RuntimeProjectionPlaneMetadata.plane_shape values must be positive."
            )
        if any(
            index >= size for index, size in zip(self.plane_indices, self.plane_shape)
        ):
            raise ValueError(
                "RuntimeProjectionPlaneMetadata.plane_indices must be within "
                f"plane_shape, got {self.plane_indices!r} for {self.plane_shape!r}."
            )
        if any(index < 0 for index in self.source_plane_indices):
            raise ValueError(
                "RuntimeProjectionPlaneMetadata.source_plane_indices cannot be negative."
            )

    @property
    def carries_source_plane_identity(self) -> bool:
        """Return whether the projected plane already selected source identity."""
        return bool(self.source_plane_indices)


class RuntimeProjectionSourceIdentityError(ValueError):
    """Raised when runtime-slice projection cannot preserve source identity."""


class RuntimeProjectionSourceIdentityRequirement(ABC):
    """How strictly each projected runtime slice must carry source identity."""

    @classmethod
    @abstractmethod
    def validate_stack_value(
        cls,
        value: "RuntimeProjectionData",
        slice_count: int,
        *,
        source_description: str,
    ) -> None:
        """Validate whether projected stack slices can be addressed."""

    @classmethod
    def project_payload_items(
        cls,
        request: RuntimeProjectionSourceIdentityRequest,
    ) -> tuple["RuntimeProjectedPayloadItem", ...]:
        """Return the request's value projected onto its runtime slices."""
        value = request.value
        slice_count = request.runtime_slice_count()
        if slice_count is None:
            return (
                RuntimeProjectedPayloadItem(
                    value=value,
                    source_description=request.source_description,
                ),
            )
        cls.validate_stack_value(
            value,
            slice_count,
            source_description=request.source_description,
        )
        projection = request.plane_projection or RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=slice_count,
        )
        items: list[RuntimeProjectedPayloadItem] = []
        for slice_index in range(slice_count):
            context = projection.selected_plane(slice_index)
            items.append(
                RuntimeProjectedPayloadItem(
                    value=request.projected_value(context),
                    source_description=request.slice_description(slice_index),
                    runtime_plane_metadata=request.plane_metadata(context),
                )
            )
        return tuple(items)


class OptionalSourceIdentity(RuntimeProjectionSourceIdentityRequirement):
    """Projected slices may omit per-slice source identity."""

    @classmethod
    def validate_stack_value(
        cls,
        value: "RuntimeProjectionData",
        slice_count: int,
        *,
        source_description: str,
    ) -> None:
        del value, slice_count, source_description


class RequiredSourceComponentMetadata(RuntimeProjectionSourceIdentityRequirement):
    """Each projected slice must carry its source component metadata."""

    @classmethod
    def validate_stack_value(
        cls,
        value: "RuntimeProjectionData",
        slice_count: int,
        *,
        source_description: str,
    ) -> None:
        validate_source_plane_component_metadata(
            value,
            slice_count,
            source_description=source_description,
        )


@dataclass(frozen=True, slots=True)
class RuntimeProjectedPayloadItem:
    """One runtime payload projected into an execution-addressable value."""

    value: RuntimeProjectionData
    source_description: str
    runtime_plane_metadata: RuntimeProjectionPlaneMetadata | None = None

    @property
    def data(self) -> RuntimeProjectionData:
        return self.value.data if isinstance(self.value, ImagePayload) else self.value

    @property
    def metadata(self) -> ImagePayloadMetadata:
        """Image metadata of the item; items of non-image kinds carry none."""
        if isinstance(self.value, ImagePayload):
            return self.value.metadata
        return ImagePayloadMetadata()

    @property
    def source_component_metadata(self) -> SourceComponentMetadata | None:
        return self.metadata.source_component_metadata

    def require_source_component_metadata(self) -> SourceComponentMetadata:
        metadata = self.source_component_metadata
        if metadata is None:
            raise ValueError(
                "Runtime payload projection requires source component metadata "
                f"for {self.source_description}."
            )
        return metadata


def validate_source_plane_component_metadata(
    value: RuntimeProjectionData,
    slice_count: int,
    *,
    source_description: str,
) -> None:
    """Require one source component-metadata record per projected slice."""
    plane_metadata = (
        value.metadata
        .with_indexed_source_plane_provenance(slice_count)
        .source_image_provenance_planes.component_metadata
    )
    if not plane_metadata or any(item is None for item in plane_metadata):
        raise RuntimeProjectionSourceIdentityError(
            "Runtime payload stack projection requires complete per-slice "
            f"component metadata for {source_description}; refusing to drop "
            "unaddressed slices."
        )
    if len(plane_metadata) == slice_count:
        return
    raise RuntimeProjectionSourceIdentityError(
        "Runtime payload stack metadata cardinality mismatch: "
        f"{len(plane_metadata)} metadata entries for {slice_count} runtime "
        f"slices in {source_description}."
    )




class RuntimeSliceProjection:
    """Runtime-slice projection at the boundary between owned and foreign values.

    Owned runtime values answer through ``RuntimeSliceProjectableValue``.
    Tuples and lists project item by item; other foreign values (arrays,
    mappings, primitives, enums) carry no runtime-slice axis.
    """

    FOREIGN_VALUE_TYPES: tuple[type, ...] = (
        np.ndarray,
        Mapping,
        str,
        bytes,
        bytearray,
        int,
        float,
        Enum,
        DtypeConversionConfig,
        type(None),
    )

    @classmethod
    def require_foreign_value(cls, value: RuntimeProjectionData) -> None:
        """Reject an owned-looking value that declares no slice behaviour."""
        if isinstance(value, cls.FOREIGN_VALUE_TYPES) or is_array_payload(value):
            return
        raise RuntimeSliceProjectionDeclarationError(
            "Runtime-slice projection has no declaration for "
            f"{type(value).__name__}; owned runtime values must implement "
            "RuntimeSliceProjectableValue."
        )

    @classmethod
    def full_stack_value(cls, value: RuntimeProjectionData) -> RuntimeProjectionData:
        """Materialize declared alignment; preserve opaque whole-stack arguments."""
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.full_stack_value()
        return value

    @classmethod
    def full_stack_kwargs(
        cls, kwargs: Mapping[str, RuntimeProjectionData]
    ) -> dict[str, RuntimeProjectionData]:
        return {name: cls.full_stack_value(value) for name, value in kwargs.items()}

    @classmethod
    def aligned_value(
        cls, value: Any, resolver: AlignedImageStackKwargResolver,
    ) -> Any:
        """Bind one value beside one slice of an aligned image stack."""
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.aligned_value(resolver)
        if isinstance(value, tuple):
            return tuple(resolver.resolve(item) for item in value)
        return value

    @classmethod
    def declared_plane_axis(cls, value: RuntimeProjectionData) -> RuntimePlaneAxis | None:
        """Return the leading plane axis a value declares; foreign values declare none."""
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.declared_plane_axis
        return None

    @classmethod
    def alignment_slices(cls, value: RuntimeProjectionData) -> tuple[Any, ...]:
        """Return a value split into the slices of an aligned invocation."""
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.alignment_slices()
        return (value,)

    @classmethod
    def output_slices(cls, value: RuntimeProjectionData) -> tuple[Any, ...]:
        """Return the scalar values one output value publishes."""
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.output_slices()
        return (value,)

    @classmethod
    def preserved_context_for_value(
        cls,
        value: RuntimeProjectionData,
    ) -> RuntimePlaneAxisValueProjection | None:
        """Return the preserved runtime-slice coordinate declared by ``value``."""
        slice_count = cls.slice_count_from_values((value,))
        if slice_count is None:
            return None
        return RuntimePlaneAxisValueProjection.preserve(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            axis_size=slice_count,
        )

    @classmethod
    def value_for_singleton_slice(
        cls,
        value: RuntimeProjectionData,
        *,
        source_description: str,
    ) -> RuntimeProjectionData:
        """Consume one payload-declared singleton runtime-slice axis."""

        projection = cls.preserved_context_for_value(value)
        if projection is None:
            raise RuntimeSliceProjectionDeclarationError(
                f"{source_description} has no declared runtime-slice axis."
            )
        if projection.axis_size != 1:
            raise ValueError(
                f"{source_description} must declare exactly one runtime slice "
                f"before its axis can be consumed, got {projection.axis_size}."
            )
        return cls.value_for_slice(value, projection.selected_plane(0))

    @classmethod
    def context_for_value(
        cls,
        value: RuntimeProjectionData,
        *,
        slice_index: int,
        slice_count: int | None = None,
    ) -> RuntimePlaneAxisValueProjection | None:
        effective_slice_count = (
            slice_count
            if slice_count is not None
            else cls.slice_count_from_values((value,))
        )
        if effective_slice_count is None:
            return None
        return RuntimePlaneAxisValueProjection.from_selected_plane(
            axis=RuntimePlaneAxis.RUNTIME_SLICE,
            plane_index=slice_index,
            axis_size=effective_slice_count,
        )

    @classmethod
    @overload
    def value_for_slice(
        cls,
        value: ObjectLabelValue,
        context: RuntimePlaneAxisValueProjection,
    ) -> ObjectLabelValue: ...

    @classmethod
    @overload
    def value_for_slice(
        cls,
        value: RuntimeProjectionData,
        context: RuntimePlaneAxisValueProjection,
    ) -> RuntimeProjectionData: ...

    @classmethod
    def value_for_slice(
        cls,
        value: RuntimeProjectionData,
        context: RuntimePlaneAxisValueProjection,
    ) -> RuntimeProjectionData:
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.value_for_slice(context)
        if isinstance(value, (tuple, list)):
            projected = [cls.value_for_slice(item, context) for item in value]
            return tuple(projected) if isinstance(value, tuple) else projected
        cls.require_foreign_value(value)
        return value

    @classmethod
    def identity_projected_value(
        cls,
        value: RuntimeProjectionData,
        context: RuntimePlaneAxisValueProjection,
    ) -> RuntimeProjectionData:
        """Project execution-slice identity recursively through nested outputs."""
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.identity_projected_value(context)
        if not isinstance(value, (tuple, list)):
            cls.require_foreign_value(value)
            return value
        projected_items = tuple(
            cls.identity_projected_value(item, context) for item in value
        )
        if all(
            projected_item is item
            for projected_item, item in zip(projected_items, value, strict=True)
        ):
            return value
        if isinstance(value, tuple):
            return projected_items
        return list(projected_items)

    @classmethod
    def object_label_endpoint(
        cls,
        value: RuntimeProjectionData,
        *,
        context: RuntimePlaneAxisValueProjection | None = None,
    ) -> RuntimeProjectionData:
        """Resolve one object-label endpoint through runtime-slice semantics."""
        if context is None:
            return value
        return cls.value_for_slice(value, context)

    @classmethod
    def kwargs_for_slice(
        cls,
        kwargs: Mapping[str, RuntimeProjectionData],
        context: RuntimePlaneAxisValueProjection,
    ) -> dict[str, RuntimeProjectionData]:
        return {
            name: cls.value_for_slice(value, context) for name, value in kwargs.items()
        }

    @classmethod
    def slice_count_from_kwargs(
        cls,
        kwargs: Mapping[str, RuntimeProjectionData],
    ) -> int | None:
        return cls.slice_count_from_values(kwargs.values())

    @classmethod
    def slice_count_for_value(cls, value: RuntimeProjectionData) -> int | None:
        if isinstance(value, RuntimeSliceProjectableValue):
            return value.runtime_slice_count()
        if isinstance(value, (tuple, list)):
            return cls.slice_count_from_values(value)
        cls.require_foreign_value(value)
        return None

    @classmethod
    def slice_count_from_values(
        cls,
        values: Iterable[RuntimeProjectionData],
    ) -> int | None:
        declared_slice_counts = {
            count
            for value in values
            for count in (cls.slice_count_for_value(value),)
            if count is not None
        }
        return cls.single_slice_count(
            declared_slice_counts,
            source_description="declared runtime-slice values",
        )

    @staticmethod
    def single_slice_count(
        slice_counts: set[int],
        *,
        source_description: str,
    ) -> int | None:
        if not slice_counts:
            return None
        if len(slice_counts) > 1:
            raise ValueError(
                f"Conflicting runtime slice counts from {source_description}."
            )
        return next(iter(slice_counts))
