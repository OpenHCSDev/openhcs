"""What Cellpose cannot state for itself; everything else is read from Cellpose."""

from dataclasses import asdict
from operator import attrgetter
from pathlib import Path
from typing import Optional

import torch
from cellpose import denoise, dynamics, metrics, models, train, transforms, utils

from openhcs.core.vfs_protocol import PlateInputFile, PlateOutputDirectory
from openhcs.processing.backends.lib_registry.model_library import (
    Converted,
    EachPlane,
    Forwarded,
    FromEarlierStep,
    Image,
    ImageStack,
    Labels,
    Library,
    ListOfPlanes,
    Measurements,
    OneImage,
    Pixels,
    PlanesWithOneResult,
    Required,
    Resource,
    RowsAlong,
    SameControl,
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
_probabilities = Stated(tuple[float, ...], list)
_not_from_files = Supplied("The step's images and labels are given as arrays.")
_no_second_set = Supplied("A step has one image stack; no test set can be given.")


def _made(directory: Path) -> str:
    """Cellpose makes ``models`` inside the directory, but not the directory."""

    directory.mkdir(parents=True, exist_ok=True)
    return str(directory)


# One image's result: masks, flows = (RGB, flow field with channels first, cell
# probability), styles, then the diameter or the restored image.
_labels = Labels("cellpose_labels", Pixels((0,)), like=Pixels((1, 2)))
_probability = Image("cell_probability", Pixels((1, 2)))
_flow_field = Image("flow_field", Pixels((1, 1), channel_axis=0))
_segmentation = (_probability, _flow_field, Image("flow_rgb", Pixels((1, 0), -1)), _labels)
_true_labels = FromEarlierStep(Labels("true_labels", Pixels(()), like=Pixels(())))

library = Library(
    __name__,
    statements={
        "x": ImageStack(),
        "train_data": ImageStack(),
        "device": Supplied("Cellpose's own gpu control chooses the device."),
        "progress": Supplied("A Qt progress bar of Cellpose's own GUI."),
        "p": Supplied("Cellpose follows the flows itself when it is not given."),
        "model_type": _segmentation_model,
        "seg_model_type": _segmentation_model,
        "pretrained_model": _model_file,
        "pretrained_model_ortho": _model_file,
        "channels": Stated(tuple[int, int], list, tuple),
        # Cellpose mutates its module-level defaults; the complete dict is passed.
        "normalize": Stated(
            NormalizeOptions, asdict, lambda on: NormalizeOptions(normalize=on)
        ),
        "resize": Stated(tuple[int, int], list),
        "scale_range": Stated(float, float),
        "lam": Stated(tuple[float, float, float], list, tuple),
        "save_path": Required(PlateOutputDirectory, _made),
        **dict.fromkeys(("train_probs", "test_probs"), _probabilities),
        **dict.fromkeys(("test_data", "test_labels"), _no_second_set),
        **dict.fromkeys(
            ("train_files", "train_labels_files", "test_files", "test_labels_files"),
            _not_from_files,
        ),
        **dict.fromkeys(
            ("masks", "masks_pred", "train_labels"), FromEarlierStep(_labels)
        ),
        "masks_true": _true_labels,
        **dict.fromkeys(("dP", "flows"), FromEarlierStep(_flow_field)),
        "cellprob": FromEarlierStep(_probability),
    },
    one_image_when_set=("z_axis", "channel_axis"),
)

_model = library.call(models.CellposeModel)
_segment = library.call(models.CellposeModel.eval, {"self": Resource(_model)})
_with_size_model = library.call(models.Cellpose)


def _measurements(**columns: tuple[int, ...]) -> Measurements:
    return Measurements("measurements", columns, counted=(0,))


library.function("segment", _segment, *_segmentation, _measurements(style=(2,)))
library.function(
    "segment_estimating_diameter",
    library.call(
        models.Cellpose.eval,
        {"self": Resource(_with_size_model), "kwargs": Forwarded(_segment)},
    ),
    *_segmentation,
    _measurements(style=(2,), diameter=(3,)),
)
_diameters = Measurements("diameters", {"diameter": (0,), "diameter_from_style": (1,)})
# Cellpose pairs a built-in model with its size model only inside models.Cellpose.
library.function(
    "estimate_diameter",
    library.call(models.SizeModel.eval, {"self": Resource(_with_size_model, "sz")}),
    _diameters,
)
_size_model = library.call(
    models.SizeModel,
    {
        "cp_model": Resource(_model),
        "pretrained_size": Required(PlateInputFile, str),
        "kwargs": Supplied("Passed to object(), which takes none."),
    },
)
library.function(
    "estimate_diameter_with_size_model_file",
    library.call(models.SizeModel.eval, {"self": Resource(_size_model)}),
    _diameters,
)
_restorer = library.call(denoise.DenoiseModel, {"model_type": _restoration_model})
library.function(
    "restore",
    library.call(denoise.DenoiseModel.eval, {"self": Resource(_restorer)}),
    main=Pixels((), channel_axis=-1),
)
_restoring_segmenter = library.call(
    denoise.CellposeDenoiseModel, {"restore_type": _restoration_model}
)
library.function(
    "restore_and_segment",
    library.call(
        denoise.CellposeDenoiseModel.eval, {"self": Resource(_restoring_segmenter)}
    ),
    *_segmentation,
    _measurements(style=(2,)),
    main=Pixels((3,), channel_axis=-1),
)

# Training returns the saved file and the loss of each epoch; the network is
# built for the call and saved under save_path by Cellpose.
_losses = RowsAlong("losses", {"train_loss": (1,), "test_loss": (2,)}, along="epoch")
_trained_model = library.call(
    models.CellposeModel, {"pretrained_model": Required(PlateInputFile, str)}
)
for name, call, *outputs in (
    (
        "train_segmentation",
        library.call(train.train_seg, {"net": Resource(_model, "net", shared=False)}),
        _losses,
    ),
    (
        # Cellpose writes the size model beside the model file it is given.
        "train_size",
        library.call(
            train.train_size,
            {
                "net": Resource(_trained_model, "net", shared=False),
                "pretrained_model": SameControl(str),
            },
        ),
    ),
    (
        # It wants planes with a channel axis and labels as flows, and reports
        # the loss of the first ten epochs and of every fifth after them.
        "train_restoration",
        library.call(
            denoise.train,
            {
                "net": Resource(_restorer, "net", shared=False),
                "train_data": Converted(
                    ImageStack(), lambda planes: [plane[None] for plane in planes]
                ),
                "train_labels": Converted(
                    FromEarlierStep(_labels),
                    lambda labels: dynamics.labels_to_flows(labels, device=torch.device("cpu")),
                ),
            },
        ),
        RowsAlong("losses", {"train_loss": (1,)}, along="report"),
    ),
):
    library.function(name, call, *outputs, use=PlanesWithOneResult())

# Plain functions of masks and flows, under Cellpose's own names: what each is
# given (every plane in its own call unless said) and what its result is.
_new_labels = (
    Measurements("object_counts", {}, counted=()),
    Labels("cellpose_labels", Pixels(()), like=Pixels(())),
)
_per_object = {"along": "object"}
for function, use, *outputs in (
    (dynamics.resize_and_compute_masks, EachPlane(), *_new_labels),
    (dynamics.compute_masks, EachPlane(), *_new_labels),
    (dynamics.remove_bad_flow_masks, EachPlane(), *_new_labels),
    (utils.remove_edge_masks, EachPlane(), *_new_labels),
    (utils.dilate_masks, EachPlane(), *_new_labels),
    (utils.fill_holes_and_remove_small_masks, EachPlane(), *_new_labels),
    (utils.stitch3D, OneImage(), *_new_labels),
    (dynamics.masks_to_flows, EachPlane(), Image("flow_field", Pixels((), 0))),
    (utils.masks_to_outlines, EachPlane(), Image("outlines", Pixels(()))),
    (utils.masks_to_edges, EachPlane(), Image("edges", Pixels(()))),
    (utils.distance_to_boundary, EachPlane(), Image("boundary_distance", Pixels(()))),
    (
        utils.diameters,
        EachPlane(),
        RowsAlong("diameters", {"median_diameter": (0,), "diameter": (1,)}, **_per_object),
    ),
    (
        utils.get_mask_compactness,
        EachPlane(),
        RowsAlong("compactness", {"compactness": ()}, **_per_object),
    ),
    (
        utils.get_mask_perimeters,
        EachPlane(),
        RowsAlong("perimeters", {"perimeter": ()}, **_per_object),
    ),
    (
        utils.size_distribution,
        EachPlane(),
        Measurements("size_distribution", {"size_distribution": ()}),
    ),
    (
        metrics.mask_ious,
        EachPlane(),
        RowsAlong("ious", {"iou": (0,), "matched_prediction": (1,)}, **_per_object),
    ),
    (
        metrics.aggregated_jaccard_index,
        ListOfPlanes(),
        Measurements("jaccard", {"aggregated_jaccard_index": ()}),
    ),
):
    library.function(function.__name__, library.call(function), *outputs, use=use)
library.function(
    "average_precision",
    library.call(
        metrics.average_precision, {"threshold": Stated(tuple[float, ...], list, tuple)}
    ),
    Measurements(
        "average_precision",
        dict(zip(("average_precision", "true_positives", "false_positives", "false_negatives"), ((0,), (1,), (2,), (3,)))),
    ),
)

globals().update(library.functions)
