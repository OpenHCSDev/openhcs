"""Image results that explicitly project their invocation's source identity."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass, replace

import numpy as np
from metaclass_registry import AutoRegisterMeta

from openhcs.core.aligned_image_payload import (
    AlignedImageStack,
    stack_image_payloads,
)
from openhcs.core.registry_strategies import NominalTypeKeyedStrategyMixin
from openhcs.core.runtime_array_values import (
    DataBackedRuntimeArrayPayload,
    RuntimeArrayData,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadataCarrier,
    ImagePayloadMetadataCompositionMode,
    image_payload_data,
    image_payload_metadata,
    image_payload_slice_context,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
)
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_alignment import (
    RuntimeSliceAlignedValueSet,
    RuntimeSliceAlignedValues,
)
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection


class SourceProjectedImageOutput(DataBackedRuntimeArrayPayload, ABC):
    """A result whose declaration proves its source-context transformation."""

    @abstractmethod
    def resolve_source_context(
        self,
        source: RuntimeArrayData,
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        """Validate and attach the source context declared by this result."""


class SourcePlaneSelectionImageOutput(SourceProjectedImageOutput):
    """A projection that retains an exact ordered subset of source planes."""

    @abstractmethod
    def selected_source_plane_indices(self) -> tuple[int, ...]:
        """Return the exact ordered source planes represented by this result."""

    def __post_init__(self) -> None:
        indices = self.selected_source_plane_indices()
        if not indices or len(set(indices)) != len(indices):
            raise ValueError("Selected source planes must be nonempty and distinct.")
        if any(type(index) is not int or index < 0 for index in indices):
            raise ValueError(
                "Selected source planes must be nonnegative integer indices."
            )
        if len(self.data.shape) != 3 or self.data.shape[0] != len(indices):
            raise ValueError(
                "Selected image output must contain one plane per source index."
            )

    def resolve_source_context(
        self,
        source: RuntimeArrayData,
        projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        """Attach selected provenance, consuming an explicitly singleton axis."""
        projection = RuntimePlaneAxisValueProjection.require_complete_projection(
            projection, value_name="Selecting source planes"
        )
        indices = self.selected_source_plane_indices()
        if any(index >= projection.axis_size for index in indices):
            raise ValueError("Selected source plane is outside the input stack.")
        source_metadata = image_payload_metadata(source)
        metadata = source_metadata.for_source_planes(indices)
        # A spatial crop owns new pixel geometry; source plane identity survives.
        metadata = metadata.without_spatial_domain().replace_fields(
            plane_axis=projection.axis,
            source_image_provenance_planes=source_metadata.source_image_provenance_planes.select(
                indices
            ),
        )
        if len(indices) == 1:
            return metadata.for_leading_source_plane(0).payload_with(self.data[0])
        return metadata.payload_with(self.data, None)


@dataclass(frozen=True)
class SelectedPlaneImageOutput(SourcePlaneSelectionImageOutput):
    """A cropped array retaining an explicit ordered subset of source planes."""

    data: RuntimeArrayData
    source_indices: tuple[int, ...]

    def with_data(self, data: RuntimeArrayData) -> "SelectedPlaneImageOutput":
        return replace(self, data=data)

    def selected_source_plane_indices(self) -> tuple[int, ...]:
        """Provide this declaration's exact source-selection proof."""
        return self.source_indices


class ImageOutputSourceContextStrategy(
    NominalTypeKeyedStrategyMixin,
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Registered image-output contextualization by semantic source payload type."""

    __registry_key__ = "value_type_label"
    __skip_if_no_key__ = True

    @classmethod
    def for_source_payload(
        cls,
        source_payload: RuntimeArrayData,
    ) -> "ImageOutputSourceContextStrategy":
        strategy = cls.for_nominal_value(source_payload)
        if strategy is None:
            return DefaultImageOutputSourceContextStrategy()
        return strategy

    def requires_plane_contextualization(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> bool:
        """Return whether this source type must bind an undeclared output axis."""

        del source_payload, output_value, plane_projection
        return False

    @abstractmethod
    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        """Return image output with source semantics attached."""


class DefaultImageOutputSourceContextStrategy(ImageOutputSourceContextStrategy):
    """Attach scalar source-image context to a derived image output."""

    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        if isinstance(output_value, AlignedImageStack):
            return output_value
        return image_payload_metadata(source_payload).derive_payload(
            source_payload,
            output_value,
            plane_projection=plane_projection,
        )


class AlignedImageStackOutputSourceContextStrategy(ImageOutputSourceContextStrategy):
    """Preserve aligned multi-source image payloads as their own source context."""

    value_type = AlignedImageStack

    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        del source_payload, plane_projection
        return output_value


class RuntimeSliceAlignedImageOutputSourceContextStrategy(
    ImageOutputSourceContextStrategy
):
    """Attach per-runtime-slice source context to derived image outputs."""

    value_type = RuntimeSliceAlignedValueSet

    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        source_values = source_payload
        if not isinstance(source_values, RuntimeSliceAlignedValueSet):
            raise TypeError(
                "Runtime-slice-aligned image output strategy requires "
                f"RuntimeSliceAlignedValueSet, got {type(source_values).__name__}."
            )
        output_data = image_payload_data(output_value)
        if plane_projection is None:
            if source_values.slice_count != 1:
                raise ValueError(
                    "Runtime-slice-aligned image output has multiple source values "
                    "but no declared runtime plane projection."
                )
            source_value = source_values.value_for_aligned_slice(0, 1)
            return image_payload_metadata(source_value).derive_payload(
                source_value,
                output_value,
            )
        output_slices = self.output_slices(
            output_value,
            output_data,
            source_values,
            plane_projection,
        )
        contextualized_slices = []
        for slice_index, output_slice in enumerate(output_slices):
            source_value = source_values.value_for_aligned_slice(
                slice_index,
                len(output_slices),
            )
            contextualized_slices.append(
                image_payload_metadata(source_value).derive_payload(
                    source_value,
                    output_slice,
                )
            )
        return stack_image_payloads(
            tuple(contextualized_slices),
            metadata_mode=ImagePayloadMetadataCompositionMode.STACK,
        )

    @staticmethod
    def output_slices(
        output_value: RuntimeArrayData,
        output_data: RuntimeArrayData,
        source_values: RuntimeSliceAlignedValueSet,
        plane_projection: RuntimePlaneAxisValueProjection,
    ) -> tuple[RuntimeArrayData, ...]:
        output_array = np.asarray(output_data)
        projection = plane_projection
        if projection.axis_size != source_values.slice_count:
            raise ValueError(
                "Runtime-slice image output projection must exactly match its "
                f"aligned source count: {projection.axis_size} != "
                f"{source_values.slice_count}."
            )
        projection.validate_shape(
            output_array.shape,
            value_name="Runtime-slice-aligned image output",
        )
        return tuple(
            image_payload_slice_context(
                output_value,
                output_array[slice_index],
                slice_index,
                plane_axis=projection.axis,
            )
            for slice_index in range(projection.axis_size)
        )


class ObjectLabelImageOutputSourceContextStrategy(ImageOutputSourceContextStrategy):
    """Project an image rendered from labels onto the invocation plane axis."""

    value_type = ObjectLabelValue

    def requires_plane_contextualization(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> bool:
        """Require projection for a volume label payload, including depth one."""

        del output_value
        if not isinstance(source_payload, ObjectLabelValue):
            raise TypeError(
                "Object-label image output context requires ObjectLabelValue, got "
                f"{type(source_payload).__name__}."
            )
        return (
            plane_projection is not None
            and plane_projection.plane_index is None
            and image_payload_metadata(source_payload).plane_axis is None
            and not image_payload_metadata(source_payload).persists_whole_image()
            and np.ndim(object_label_dense_array(source_payload)) >= 3
        )

    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData:
        if not isinstance(source_payload, ObjectLabelValue):
            raise TypeError(
                "Object-label image output context requires ObjectLabelValue, got "
                f"{type(source_payload).__name__}."
            )
        source_metadata = image_payload_metadata(source_payload)
        if source_metadata.persists_whole_image():
            return source_metadata.derive_payload(
                source_payload,
                output_value,
                plane_projection=None,
            )
        if plane_projection is None or plane_projection.plane_index is not None:
            return source_metadata.derive_payload(
                source_payload,
                output_value,
                plane_projection=plane_projection,
            )
        plane_count = source_metadata.source_provenance.source_plane_count
        if plane_count != plane_projection.axis_size:
            raise ValueError(
                "Object-label image output source-plane provenance must match the "
                "declared runtime plane axis: "
                f"{plane_count} != {plane_projection.axis_size}."
            )
        plane_projection.validate_shape(
            np.shape(image_payload_data(output_value)),
            value_name="Object-label image output payload",
        )
        output_metadata = image_payload_metadata(output_value)
        contextualized_output = output_metadata.replace_fields(
            plane_axis=plane_projection.axis,
        ).attach_to(output_value)
        return source_metadata.derive_payload(
            source_payload,
            contextualized_output,
            plane_projection=plane_projection,
        )


class ObjectLabelOutputValueContextStrategy(
    NominalTypeKeyedStrategyMixin,
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Registered object-label output contextualization by nominal value type."""

    __registry_key__ = "value_type_label"
    __skip_if_no_key__ = True

    @classmethod
    def for_output_value(
        cls,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
    ) -> "ObjectLabelOutputValueContextStrategy":
        return cls.require_nominal_value(
            output_value,
            context="Object-label function output",
        )

    @abstractmethod
    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet:
        """Return the output with source-image context attached when possible."""


class RuntimeSliceAlignedObjectLabelOutputValueContextStrategy(
    ObjectLabelOutputValueContextStrategy
):
    """Contextualize each runtime-slice-aligned object-label output slice."""

    value_type = RuntimeSliceAlignedValueSet

    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet:
        aligned_values = output_value
        if not isinstance(aligned_values, RuntimeSliceAlignedValueSet):
            raise TypeError(
                "Runtime-slice-aligned object-label output strategy requires "
                f"RuntimeSliceAlignedValueSet, got {type(aligned_values).__name__}."
            )
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
        if plane_projection.axis_size != aligned_values.slice_count:
            raise ValueError(
                "Runtime-slice-aligned object-label output count must exactly "
                "match the declared runtime plane axis: "
                f"{aligned_values.slice_count} != {plane_projection.axis_size}."
            )
        return RuntimeSliceAlignedValues(
            tuple(
                ObjectLabelOutputValueContextStrategy.for_output_value(
                    aligned_values.value_for_slice(slice_index)
                ).contextualize(
                    RuntimeSliceProjection.value_for_slice(
                        source_payload,
                        RuntimePlaneAxisValueProjection.from_selected_plane(
                            axis=plane_projection.axis,
                            plane_index=slice_index,
                            axis_size=plane_projection.axis_size,
                        ),
                    ),
                    aligned_values.value_for_slice(slice_index),
                    None,
                )
                for slice_index in range(aligned_values.slice_count)
            )
        )


class ContextualObjectLabelOutputValueContextStrategy(
    ObjectLabelOutputValueContextStrategy
):
    """Preserve object-label domain while filling missing source-image context."""

    value_type = ObjectLabelValue

    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> ObjectLabelValue:
        del plane_projection
        if not isinstance(output_value, ObjectLabelValue):
            raise TypeError(
                "Contextual object-label output strategy requires "
                f"ObjectLabelValue, got {type(output_value).__name__}."
            )
        return output_value.with_source_image_context(
            source_payload
        ).with_parent_image_context(source_payload)


class DenseArrayObjectLabelOutputValueContextStrategy(
    ObjectLabelOutputValueContextStrategy
):
    """Build declared object labels through the existing source-domain owner."""

    def contextualize(
        self,
        source_payload: RuntimeArrayData,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
        plane_projection: RuntimePlaneAxisValueProjection | None,
    ) -> ObjectLabelValue:
        return SourceImageObjectLabelBuildRequest(
            image=source_payload,
            labels=self.label_array(output_value),
            plane_projection=plane_projection,
        ).payload()

    @abstractmethod
    def label_array(
        self,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
    ) -> object:
        """Project the dense label data owned by this nominal value case."""


class NumpyArrayObjectLabelOutputValueContextStrategy(
    DenseArrayObjectLabelOutputValueContextStrategy
):
    """Build object-label context for declared NumPy array outputs."""

    value_type = np.ndarray

    def label_array(
        self,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
    ) -> object:
        return output_value


class ImagePayloadObjectLabelOutputValueContextStrategy(
    DenseArrayObjectLabelOutputValueContextStrategy
):
    """Consume a declared label array with its preserved runtime plane carrier."""

    value_type = ImagePayloadMetadataCarrier

    def label_array(
        self,
        output_value: RuntimeArrayData | ObjectLabelValue | RuntimeSliceAlignedValueSet,
    ) -> object:
        return image_payload_data(output_value)
