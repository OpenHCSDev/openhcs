"""Small physical NGFF fixtures covering both supported storage formats."""

from pathlib import Path

import numpy as np
import zarr
from ome_zarr.format import Format, FormatV04, FormatV05

NGFF_FORMATS = (FormatV04(), FormatV05())


def write_ngff_plate(
    path: Path,
    pixels: np.ndarray,
    *,
    fmt: Format = NGFF_FORMATS[0],
    plate_name: str = "Plate:mixed",
) -> None:
    root = zarr.open_group(str(path), mode="w", zarr_format=fmt.zarr_format)
    well = root.require_group("A/01")
    image = well.require_group("0")
    axes = [
        {"name": "t", "type": "time"},
        {"name": "c", "type": "channel"},
        {"name": "z", "type": "space", "unit": "micrometer"},
        {"name": "y", "type": "space", "unit": "micrometer"},
        {"name": "x", "type": "space", "unit": "micrometer"},
    ]
    image_pixels = pixels.reshape((1,) * (len(axes) - pixels.ndim) + pixels.shape)
    metadata = (
        (
            root,
            "plate",
            {
                "columns": [{"name": "01"}],
                "name": plate_name,
                "rows": [{"name": "A"}],
                "wells": [{"columnIndex": 0, "path": "A/01", "rowIndex": 0}],
            },
        ),
        (well, "well", {"images": [{"path": "0"}]}),
        (
            image,
            "multiscales",
            [
                {
                    "axes": axes,
                    "datasets": [
                        {
                            "coordinateTransformations": [
                                {"scale": [1.0] * 5, "type": "scale"}
                            ],
                            "path": "0",
                        }
                    ],
                    "name": "Image:ngff",
                }
            ],
        ),
    )
    for group, key, value in metadata:
        if fmt.zarr_format == 3:
            group.attrs["ome"] = {"version": fmt.version, key: value}
        else:
            declaration = value[0] if isinstance(value, list) else value
            declaration["version"] = fmt.version
            group.attrs[key] = value
    omero = {
        "channels": [
            {"label": "NGFF" if index == 0 else f"NGFF-{index + 1}"}
            for index in range(image_pixels.shape[1])
        ]
    }
    array_options = {}
    if fmt.zarr_format == 3:
        image.attrs["ome"] = {**image.attrs["ome"], "omero": omero}
        array_options["dimension_names"] = tuple(axis["name"] for axis in axes)
    else:
        image.attrs["omero"] = omero
    array = image.create_array(
        "0",
        shape=image_pixels.shape,
        dtype=image_pixels.dtype,
        chunks=(1, 1, 1, *image_pixels.shape[-2:]),
        **array_options,
    )
    array[:] = image_pixels
