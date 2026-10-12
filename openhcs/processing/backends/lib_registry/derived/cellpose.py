"""What Cellpose cannot state for itself; everything else is read from Cellpose."""

from dataclasses import asdict
from functools import partial
from operator import attrgetter
from pathlib import Path
from typing import Optional

import torch
from cellpose import denoise, dynamics, metrics, models, train, transforms, utils

from openhcs.core.vfs_protocol import PlateInputFile, PlateOutputDirectory
from openhcs.processing.backends.lib_registry import model_library as ml

SegmentationModel = ml.enum_of_names("SegmentationModel", __name__, models.MODEL_NAMES)
RestorationModel = ml.enum_of_names("RestorationModel", __name__, denoise.MODEL_NAMES)
NormalizeOptions = ml.options_dataclass(
    "NormalizeOptions",
    __name__,
    models.normalize_default,
    transforms.normalize_img,
    stated={"lowhigh": tuple[float, float], "percentile": tuple[float, float]},
)


def _made(directory: Path) -> str:
    """Cellpose makes ``models`` inside the directory, but not the directory."""

    directory.mkdir(parents=True, exist_ok=True)
    return str(directory)


_segmentation_model = ml.Stated(SegmentationModel, attrgetter("value"), SegmentationModel)
_restoration_model = ml.Stated(RestorationModel, attrgetter("value"), RestorationModel)
_model_file = ml.Stated(Optional[PlateInputFile], str, lambda absent: None)
_required_file = ml.Required(PlateInputFile, str)

# One image's result: masks, flows = (RGB, flow field with channels first, cell
# probability), styles, then the diameter or the restored image. A plain function
# returns its one result whole.
_whole = ml.Pixels(())
_labels = ml.Labels("cellpose_labels", ml.Pixels((0,)), like=ml.Pixels((1, 2)))
_probability = ml.Image("cell_probability", ml.Pixels((1, 2)))
_flow_field = ml.Image("flow_field", ml.Pixels((1, 1), channel_axis=0))
_flow_rgb = ml.Image("flow_rgb", ml.Pixels((1, 0), channel_axis=-1))
_segmentation = (_probability, _flow_field, _flow_rgb, _labels)
_published_labels = ml.FromEarlierStep(_labels)
_published_flows = ml.FromEarlierStep(_flow_field)

library = ml.Library(
    __name__,
    statements={
        "x": ml.ImageStack(),
        "train_data": ml.ImageStack(),
        "device": ml.Supplied("Cellpose's own gpu control chooses the device."),
        "progress": ml.Supplied("A Qt progress bar of Cellpose's own GUI."),
        "p": ml.Supplied("Cellpose follows the flows itself when it is not given."),
        "model_type": _segmentation_model,
        "seg_model_type": _segmentation_model,
        "pretrained_model": _model_file,
        "pretrained_model_ortho": _model_file,
        "channels": ml.Stated(tuple[int, int], list, tuple),
        # Cellpose mutates its module-level defaults; the complete dict is passed.
        "normalize": ml.Stated(
            NormalizeOptions, asdict, lambda on: NormalizeOptions(normalize=on)
        ),
        "resize": ml.Stated(tuple[int, int], list),
        "scale_range": ml.Stated(float, float),
        "save_path": ml.Required(PlateOutputDirectory, _made),
        **dict.fromkeys(("train_probs", "test_probs"), ml.Stated(tuple[float, ...], list)),
        **dict.fromkeys(
            ("test_data", "test_labels"),
            ml.Supplied("A step has one image stack; no test set can be given."),
        ),
        **dict.fromkeys(
            ("train_files", "train_labels_files", "test_files", "test_labels_files"),
            ml.Supplied("The step's images and labels are given as arrays."),
        ),
        **dict.fromkeys(("masks", "masks_pred", "train_labels"), _published_labels),
        "masks_true": ml.FromEarlierStep(ml.Labels("true_labels", _whole, like=_whole)),
        **dict.fromkeys(("dP", "flows"), _published_flows),
        "cellprob": ml.FromEarlierStep(_probability),
    },
    one_image_when_set=("z_axis", "channel_axis"),
)

_model = library.call(models.CellposeModel)
_segment = library.call(models.CellposeModel.eval, {"self": ml.Resource(_model)})
_with_size_model = library.call(models.Cellpose)
_measurements = partial(ml.Measurements, "measurements", counted=(0,))
_diameters = ml.Measurements("diameters", {"diameter": (0,), "diameter_from_style": (1,)})

library.function("segment", _segment, *_segmentation, _measurements({"style": (2,)}))
library.function(
    "segment_estimating_diameter",
    library.call(
        models.Cellpose.eval,
        {"self": ml.Resource(_with_size_model), "kwargs": ml.Forwarded(_segment)},
    ),
    *_segmentation,
    _measurements({"style": (2,), "diameter": (3,)}),
)
# Cellpose pairs a built-in model with its size model only inside models.Cellpose.
library.function(
    "estimate_diameter",
    library.call(models.SizeModel.eval, {"self": ml.Resource(_with_size_model, "sz")}),
    _diameters,
)
_size_model = library.call(
    models.SizeModel,
    {
        "cp_model": ml.Resource(_model),
        "pretrained_size": _required_file,
        "kwargs": ml.Supplied("Passed to object(), which takes none."),
    },
)
library.function(
    "estimate_diameter_with_size_model_file",
    library.call(models.SizeModel.eval, {"self": ml.Resource(_size_model)}),
    _diameters,
)
_restorer = library.call(denoise.DenoiseModel, {"model_type": _restoration_model})
library.function(
    "restore",
    library.call(denoise.DenoiseModel.eval, {"self": ml.Resource(_restorer)}),
    main=ml.Pixels((), channel_axis=-1),
)
_restoring_segmenter = library.call(
    denoise.CellposeDenoiseModel, {"restore_type": _restoration_model}
)
library.function(
    "restore_and_segment",
    library.call(
        denoise.CellposeDenoiseModel.eval, {"self": ml.Resource(_restoring_segmenter)}
    ),
    *_segmentation,
    _measurements({"style": (2,)}),
    main=ml.Pixels((3,), channel_axis=-1),
)

# Training returns the saved file and losses; the network is built for the call
# and Cellpose saves it under save_path.
_net = partial(ml.Resource, attribute="net", shared=False)
_train = partial(library.function, use=ml.PlanesWithOneResult())
_train(
    "train_segmentation",
    library.call(train.train_seg, {"net": _net(_model)}),
    ml.RowsAlong("losses", {"train_loss": (1,), "test_loss": (2,)}, along="epoch"),
)
# Cellpose writes the size model beside the model file it is given.
_trained_model = library.call(models.CellposeModel, {"pretrained_model": _required_file})
_train(
    "train_size",
    library.call(
        train.train_size,
        {"net": _net(_trained_model), "pretrained_model": ml.SameControl(str)},
    ),
)
# Restoration training wants planes with a channel axis and labels as flows, and
# reports the loss of the first ten epochs and of every fifth after them.
_train(
    "train_restoration",
    library.call(
        denoise.train,
        {
            "net": _net(_restorer),
            "train_data": ml.Converted(
                ml.ImageStack(), lambda planes: [plane[None] for plane in planes]
            ),
            "train_labels": ml.Converted(
                _published_labels,
                partial(dynamics.labels_to_flows, device=torch.device("cpu")),
            ),
        },
    ),
    ml.RowsAlong("losses", {"train_loss": (1,)}, along="report"),
)

# Plain functions of masks and flows, under Cellpose's own names, by how they
# take the stack: what each one's result is.
_objects = partial(ml.RowsAlong, along="object")
_new_labels = (
    ml.Measurements("object_counts", {}, counted=()),
    ml.Labels("cellpose_labels", _whole, like=_whole),
)
_precision = ("average_precision", "true_positives", "false_positives", "false_negatives")
for use, results in {
    ml.EachPlane(): {
        dynamics.resize_and_compute_masks: _new_labels,
        dynamics.compute_masks: _new_labels,
        dynamics.remove_bad_flow_masks: _new_labels,
        utils.remove_edge_masks: _new_labels,
        utils.dilate_masks: _new_labels,
        utils.fill_holes_and_remove_small_masks: _new_labels,
        dynamics.masks_to_flows: [ml.Image("flow_field", ml.Pixels((), channel_axis=0))],
        utils.masks_to_outlines: [ml.Image("outlines", _whole)],
        utils.masks_to_edges: [ml.Image("edges", _whole)],
        utils.distance_to_boundary: [ml.Image("boundary_distance", _whole)],
        utils.diameters: [
            _objects("diameters", {"median_diameter": (0,), "diameter": (1,)})
        ],
        utils.get_mask_compactness: [_objects("compactness", {"compactness": ()})],
        utils.get_mask_perimeters: [_objects("perimeters", {"perimeter": ()})],
        utils.size_distribution: [
            ml.Measurements("size_distribution", {"size_distribution": ()})
        ],
        metrics.mask_ious: [_objects("ious", {"iou": (0,), "matched_prediction": (1,)})],
    },
    ml.OneImage(): {utils.stitch3D: _new_labels},
    ml.ListOfPlanes(): {
        metrics.aggregated_jaccard_index: [
            ml.Measurements("jaccard", {"aggregated_jaccard_index": ()})
        ],
        metrics.average_precision: [
            ml.Measurements(
                "average_precision", {name: (at,) for at, name in enumerate(_precision)}
            )
        ],
    },
}.items():
    for function, outputs in results.items():
        library.function(function.__name__, library.call(function), *outputs, use=use)

globals().update(library.functions)
