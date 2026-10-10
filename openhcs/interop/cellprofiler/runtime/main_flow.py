"""CellProfiler image outputs published through the OpenHCS main flow."""

from __future__ import annotations

from openhcs.core.runtime_plane_projection import RuntimePlaneAxisValueProjection
from openhcs.core.steps.function_runtime import RuntimeCallableArgument
from openhcs.core.runtime_array_values import array_geometry
from openhcs.core.runtime_image_values import owned_runtime_value


def cellprofiler_main_flow_output(
    input_image: RuntimeCallableArgument,
    output_image: RuntimeCallableArgument,
    plane_projection: RuntimePlaneAxisValueProjection | None,
) -> RuntimeCallableArgument:
    """Preserve the declared OpenHCS plane axis on a CP output image."""
    output_image = owned_runtime_value(output_image)
    output_axis = output_image.metadata.plane_axis
    if output_axis is None:
        return output_image
    if plane_projection is None:
        raise ValueError(
            "CellProfiler main-flow output declares a plane axis but the invocation "
            "supplied no plane projection."
        )
    if output_axis is not plane_projection.axis:
        raise ValueError(
            "CellProfiler main-flow output axis conflicts with the invocation "
            f"projection: {output_axis.value!r} != "
            f"{plane_projection.axis.value!r}."
        )
    plane_projection.validate_shape(
        array_geometry(output_image).shape,
        value_name="CellProfiler main-flow output",
    )
    input_axis = input_image.metadata.plane_axis
    if input_axis is not None:
        if input_axis is not plane_projection.axis:
            raise ValueError(
                "CellProfiler main-flow input axis conflicts with the output "
                f"projection: {input_axis.value!r} != "
                f"{plane_projection.axis.value!r}."
            )
        plane_projection.validate_shape(
            array_geometry(input_image).shape,
            value_name="CellProfiler input image",
        )
    if output_image.metadata.has_complete_source_identity(
        output_image,
        plane_projection,
    ):
        return output_image
    return input_image.metadata.derive_payload(
        input_image,
        output_image,
        plane_projection=plane_projection,
    )
