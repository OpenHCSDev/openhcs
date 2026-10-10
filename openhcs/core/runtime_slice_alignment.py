"""Non-image values aligned to runtime slices."""

from __future__ import annotations

from abc import abstractmethod
from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any, Generic, TypeVar

import numpy as np

from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
    RuntimeSliceProjectableValue,
)

if TYPE_CHECKING:
    from openhcs.core.aligned_image_payload import AlignedImageStackKwargResolver

SliceValueT = TypeVar("SliceValueT")
MappedValueT = TypeVar("MappedValueT")


class RuntimeSliceAlignedValueSet(RuntimeSliceProjectableValue, Generic[SliceValueT]):
    """Values carried one per runtime slice."""

    @property
    @abstractmethod
    def slice_count(self) -> int:
        """Return the number of runtime slices carried by this value."""

    @abstractmethod
    def value_at(self, slice_index: int) -> SliceValueT:
        """Return the value for one runtime slice."""

    @property
    def values(self) -> tuple[SliceValueT, ...]:
        """Return the value of every runtime slice, in slice order."""
        return tuple(self.value_at(index) for index in range(self.slice_count))

    def map_slices(
        self, transform: Callable[[SliceValueT], MappedValueT],
    ) -> "RuntimeSliceAlignedValues[MappedValueT]":
        """Apply ``transform`` to each slice's value, keeping slice alignment."""
        return RuntimeSliceAlignedValues(tuple(transform(value) for value in self.values))

    def value_for_aligned_slice(
        self,
        slice_index: int,
        slice_count: int | None,
    ) -> SliceValueT:
        """Return the value for an explicitly declared, exactly aligned slice."""
        if slice_count is None:
            raise ValueError(
                "Runtime-slice-aligned value requires a declared outer slice count."
            )
        if self.slice_count != slice_count:
            raise ValueError(
                "Runtime-slice-aligned value count must exactly match the declared "
                f"outer slice count: {self.slice_count} != {slice_count}."
            )
        if slice_index < 0 or slice_index >= slice_count:
            raise ValueError(
                "Runtime-slice-aligned value index is outside the declared outer "
                f"slice count: index {slice_index}, count {slice_count}."
            )
        return self.value_at(slice_index)

    # -- RuntimeSliceProjectableValue -------------------------------------

    def runtime_slice_count(self) -> int | None:
        return self.slice_count

    def value_for_slice(self, context: RuntimePlaneAxisValueProjection) -> Any:
        if context.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            return self
        return self.value_for_aligned_slice(
            context.require_plane_index(), context.axis_size,
        )

    def aligned_value(self, resolver: "AlignedImageStackKwargResolver") -> Any:
        return self.value_for_aligned_slice(
            resolver.projection_axis.require_plane_index(),
            resolver.projection_axis.axis_size,
        )

    def alignment_slices(self) -> tuple[SliceValueT, ...]:
        return self.values

    def project_declared_source(
        self, source_image_name: str,
    ) -> "RuntimeSliceAlignedValues[Any]":
        """Project each slice's image to one declared source image."""
        return self.map_slices(
            lambda value: value.project_declared_source(source_image_name)
        )

    # -- derived image outputs ------------------------------------------------

    def requires_output_plane_contextualization(
        self, output: Any, plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> bool:
        del output, plane_projection
        return False

    def fill_output_source_context(self, output: Any) -> Any:
        """Aligned values carry no scalar image context to fill an output from."""
        return output

    def contextualize_image_output(
        self, output: Any, plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> Any:
        """Attach each slice's source context to that slice of a derived output."""
        if plane_projection is None:
            if self.slice_count != 1:
                raise ValueError(
                    "Runtime-slice-aligned image output has multiple source values "
                    "but no declared runtime plane projection."
                )
            source = self.value_for_aligned_slice(0, 1)
            return source.contextualize_image_output(output, None)
        if plane_projection.axis_size != self.slice_count:
            raise ValueError(
                "Runtime-slice image output projection must exactly match its "
                f"aligned source count: {plane_projection.axis_size} != "
                f"{self.slice_count}."
            )
        output_array = np.asarray(output.data)
        plane_projection.validate_shape(
            output_array.shape,
            value_name="Runtime-slice-aligned image output",
        )
        from openhcs.core.aligned_image_payload import stack_image_payloads
        from openhcs.core.runtime_image_values import (
            ImagePayloadMetadataCompositionMode,
        )

        return stack_image_payloads(
            tuple(
                source.contextualize_image_output(
                    output.slice_payload(
                        output_array[index], index, plane_axis=plane_projection.axis,
                    ),
                    None,
                )
                for index, source in enumerate(self.values)
            ),
            metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
        )

    def object_label_output(
        self, source: Any, plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> "RuntimeSliceAlignedValues[Any]":
        """Build object labels for each slice from that slice of ``source``."""
        if plane_projection is None:
            raise ValueError(
                "Runtime-slice-aligned object-label output requires a declared "
                "runtime plane projection."
            )
        if plane_projection.axis is not RuntimePlaneAxis.RUNTIME_SLICE:
            raise ValueError(
                "Runtime-slice-aligned object-label output requires the "
                f"runtime-slice axis, got {plane_projection.axis.value!r}."
            )
        if plane_projection.axis_size != self.slice_count:
            raise ValueError(
                "Runtime-slice-aligned object-label output count must exactly "
                "match the declared runtime plane axis: "
                f"{self.slice_count} != {plane_projection.axis_size}."
            )
        from openhcs.core.runtime_image_values import ImagePayload
        from openhcs.core.runtime_slice_projection import RuntimeSliceProjection

        return RuntimeSliceAlignedValues(
            tuple(
                ImagePayload.of(output).object_label_output(
                    RuntimeSliceProjection.value_for_slice(
                        source, plane_projection.selected_plane(index),
                    ),
                    None,
                )
                for index, output in enumerate(self.values)
            )
        )


@dataclass(frozen=True, slots=True)
class RuntimeSliceAlignedValues(RuntimeSliceAlignedValueSet[SliceValueT]):
    """Non-image payload with one backend-native value per runtime slice."""

    slices: tuple[SliceValueT, ...]

    def __post_init__(self) -> None:
        slices = tuple(self.slices)
        if not slices:
            raise ValueError("RuntimeSliceAlignedValues.slices cannot be empty.")
        object.__setattr__(self, "slices", slices)

    @property
    def slice_count(self) -> int:
        return len(self.slices)

    @property
    def values(self) -> tuple[SliceValueT, ...]:
        return self.slices

    def value_at(self, slice_index: int) -> SliceValueT:
        return self.slices[slice_index]
