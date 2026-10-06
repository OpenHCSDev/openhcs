from tests.diagnostics.volume_projection_fixture import (ArrayPayload, numpy, ProcessingContract, artifact_outputs, SELECTED_VOLUME, SelectedPlaneImageOutput, np, image_payload_data)

@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(SELECTED_VOLUME)
def select_volume_fixture_planes_v2(
    image: ArrayPayload,
    plane_indices: tuple[int, ...] = (),
) -> SelectedPlaneImageOutput:
    """Select ordered planes through the existing source-projection owner."""
    pixels = image_payload_data(image)
    if pixels.ndim != 3:
        raise ValueError("Expected a scalar ZYX fixture")
    indices = plane_indices or tuple(range(pixels.shape[0]))
    return SelectedPlaneImageOutput(np.take(pixels, indices, axis=0), indices)
