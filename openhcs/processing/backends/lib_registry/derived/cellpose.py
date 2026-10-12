"""What Cellpose cannot state for itself; everything else is read from Cellpose."""

from dataclasses import asdict
from operator import attrgetter
from typing import Optional

from cellpose import denoise, models, transforms

from openhcs.core.vfs_protocol import PlateInputFile
from openhcs.processing.backends.lib_registry.model_library import (
    Forwarded,
    Image,
    ImageStack,
    Labels,
    Library,
    Measurements,
    Pixels,
    Resource,
    Stated,
    Supplied,
    enum_of_names,
    options_dataclass,
)

SegmentationModel = enum_of_names("SegmentationModel", __name__, models.MODEL_NAMES)
RestorationModel = enum_of_names("RestorationModel", __name__, denoise.MODEL_NAMES)
NormalizeOptions = options_dataclass(
    "NormalizeOptions",
    __name__,
    models.normalize_default,
    transforms.normalize_img,
    stated={"lowhigh": tuple[float, float], "percentile": tuple[float, float]},
)

_segmentation_model = Stated(SegmentationModel, attrgetter("value"), SegmentationModel)
_restoration_model = Stated(RestorationModel, attrgetter("value"), RestorationModel)
_model_file = Stated(Optional[PlateInputFile], str, lambda absent: None)

library = Library(
    __name__,
    statements={
        "x": ImageStack(),
        "device": Supplied("Cellpose's own gpu control chooses the device."),
        "progress": Supplied("A Qt progress bar of Cellpose's own GUI."),
        "model_type": _segmentation_model,
        "pretrained_model": _model_file,
        "pretrained_model_ortho": _model_file,
        "pretrained_size": _model_file,
        "channels": Stated(tuple[int, int], list, tuple),
        # Cellpose mutates its module-level defaults; the complete dict is passed.
        "normalize": Stated(
            NormalizeOptions, asdict, lambda on: NormalizeOptions(normalize=on)
        ),
    },
    one_image_when_set=("z_axis", "channel_axis"),
)

_model = library.call(models.CellposeModel)
_segment = library.call(models.CellposeModel.eval, {"self": Resource(_model)})

# One image's result: masks, flows = (RGB, flow field with channels first, cell
# probability), styles, then the diameter or the restored image.
_probability = Pixels((1, 2))
_segmentation = (
    Labels("labels", Pixels((0,)), like=_probability),
    Image("cell_probability", _probability),
    Image("flow_field", Pixels((1, 1), channel_axis=0)),
    Image("flow_rgb", Pixels((1, 0), channel_axis=-1)),
)


def _measurements(**columns: tuple[int, ...]) -> Measurements:
    return Measurements("measurements", __name__, columns, counted=(0,))


library.function("segment", _segment, *_segmentation, _measurements(style=(2,)))
library.function(
    "segment_estimating_diameter",
    library.call(
        models.Cellpose.eval,
        {"self": Resource(library.call(models.Cellpose)), "kwargs": Forwarded(_segment)},
    ),
    *_segmentation,
    _measurements(style=(2,), diameter=(3,)),
)
library.function(
    "estimate_diameter",
    library.call(
        models.SizeModel.eval,
        {
            "self": Resource(
                library.call(
                    models.SizeModel,
                    {
                        "cp_model": Resource(_model),
                        "kwargs": Supplied("Passed to object(), which takes none."),
                    },
                )
            )
        },
    ),
    Measurements("diameters", __name__, {"diameter": (0,), "diameter_from_style": (1,)}),
)
library.function(
    "restore",
    library.call(
        denoise.DenoiseModel.eval,
        {"self": Resource(library.call(denoise.DenoiseModel, {"model_type": _restoration_model}))},
    ),
    main=Pixels((), channel_axis=-1),
)
library.function(
    "restore_and_segment",
    library.call(
        denoise.CellposeDenoiseModel.eval,
        {
            "self": Resource(
                library.call(
                    denoise.CellposeDenoiseModel, {"restore_type": _restoration_model}
                )
            )
        },
    ),
    *_segmentation,
    _measurements(style=(2,)),
    main=Pixels((3,), channel_axis=-1),
)

globals().update(library.functions)
