from tests.diagnostics.volume_projection_fixture import (ArrayPayload, numpy, ProcessingContract, artifact_outputs, VOLUME_IMAGE, VOLUME_LABELS, VOLUME_ROWS, np, image_payload_data, image_payload_metadata, DataclassMeasurementColumnarRows, VolumeProjectionFixtureRow)

@numpy(contract=ProcessingContract.PURE_3D)
@artifact_outputs(VOLUME_IMAGE, VOLUME_LABELS, VOLUME_ROWS)
def inspect_volume_fixture_v2(
    image: ArrayPayload,
) -> tuple[ArrayPayload, ArrayPayload, DataclassMeasurementColumnarRows]:
    """Preserve the entire actual input stack when publishing labels and rows."""
    pixels = image_payload_data(image)
    if pixels.ndim != 3 or not np.issubdtype(pixels.dtype, np.integer):
        raise ValueError("Expected an integer scalar ZYX fixture")
    if np.any(pixels < 0):
        raise ValueError("Fixture object IDs must be non-negative")
    metadata = image_payload_metadata(image)
    labels = pixels.astype(np.int32, copy=True)
    rows = tuple(
        VolumeProjectionFixtureRow(index, int(label), int(np.count_nonzero(plane == label)))
        for index, plane in enumerate(labels)
        for label in np.unique(plane)
        if label != 0
    )
    return (
        metadata.payload_with(pixels.copy()),
        metadata.payload_with(labels),
        DataclassMeasurementColumnarRows(rows, row_type=VolumeProjectionFixtureRow),
    )
