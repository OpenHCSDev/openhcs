"""CellProfiler plugin RunStarDist.

Upstream: CellProfiler-plugins ``active_plugins/runstardist.py`` (settings
revision 1 at commit 5aaa4e5). The plugin has had two layouts under that one
revision number: nine rows, where ``Model`` is 2D, 3D or Custom, and fifteen
rows, where ``Model Type`` is that choice and two ``Model`` rows name the 2D
and the 3D pretrained model. Both are declared.

OpenHCS has no StarDist function, so the step converts and cannot run.
"""

from typing import TYPE_CHECKING, ClassVar

from openhcs.core.artifacts.kinds import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.callable_contract import runtime_image_execution_mode
from openhcs.core.image_payload_execution_mode import FullStackExecution
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.memory.decorators import numpy
from openhcs.core.processing_contracts import FlexibleContract
from openhcs.core.runtime_image_values import ImagePayload
from openhcs.core.runtime_object_labels import ObjectLabelValue
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    MeasurementArtifactOutputModule,
    ObjectArtifactOutputModule,
)
from openhcs.interop.cellprofiler.module_settings import BoundModuleSettings
from openhcs.interop.cellprofiler.module_without_function import (
    ModuleWithoutFunction,
    cellprofiler_binary,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock
from openhcs.interop.cellprofiler.setting_names import setting_name_matches
from openhcs.interop.cellprofiler.settings_binder import (
    ModuleOnlySettingBinding,
    SettingToKeywordBinding,
    parse_cellprofiler_float,
    parse_cellprofiler_int,
)

if TYPE_CHECKING:
    from openhcs.core.function_patterns import FunctionInvocationKey

REQUIRED_DISTRIBUTIONS = ("stardist",)

_MODEL_KINDS = ("2D", "3D")
"""The pretrained kinds, in the order of the fifteen-row layout's ``Model`` rows."""


class RunStarDistModule(
    MeasurementArtifactOutputModule,
    ObjectArtifactOutputModule,
    ModuleWithoutFunction,
):
    module_name = "RunStarDist"
    function_name = "run_stardist"
    what_openhcs_lacks = (
        "OpenHCS has no StarDist function. It needs StarDist's "
        "predict_instances as a catalogue function, with the model built by "
        "from_pretrained or from a model folder."
    )

    model_kind_setting = "Model Type"
    model_setting = "Model"
    model_folder_setting = "Model folder"
    tile_setting = "Tile input image?"
    horizontal_tiles_setting = "Horizontal tiles"
    vertical_tiles_setting = "Vertical tiles"
    save_probability_setting = "Save probability image?"

    probability_image_binding = SettingToKeywordBinding.output(
        "Name the probability image", ImageArtifactType
    )
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input("Select the input image", ImageArtifactType),
        SettingToKeywordBinding.output(
            "Name the output object", ObjectLabelsArtifactType
        ),
        SettingToKeywordBinding(
            save_probability_setting, "save_probability_image", cellprofiler_binary
        ),
        probability_image_binding,
        SettingToKeywordBinding(
            "Probability threshold", "prob_thresh", parse_cellprofiler_float
        ),
        SettingToKeywordBinding(
            "Overlap threshold", "nms_thresh", parse_cellprofiler_float
        ),
        # Read together in ``postprocess_bound_settings``.
        ModuleOnlySettingBinding(model_kind_setting),
        ModuleOnlySettingBinding(model_setting),
        ModuleOnlySettingBinding(model_folder_setting),
        ModuleOnlySettingBinding(tile_setting),
        ModuleOnlySettingBinding(horizontal_tiles_setting),
        ModuleOnlySettingBinding(vertical_tiles_setting),
    )
    ignored_settings = (
        # A limit on GPU memory is process state; device assignment owns it.
        "Manually set how much GPU memory each worker can use?",
        "GPU memory (in GB) for each worker",
    )

    @classmethod
    def active_artifact_bindings(
        cls,
        module: ModuleBlock | None,
        *,
        invocation_key: "FunctionInvocationKey | None" = None,
    ) -> tuple[SettingToKeywordBinding, ...]:
        """The probability image exists only when the pipeline saves it."""

        bindings = super().active_artifact_bindings(
            module, invocation_key=invocation_key
        )
        if module is None or cellprofiler_binary(
            cls.setting_value(module, cls.save_probability_setting) or "No"
        ):
            return bindings
        return tuple(
            binding
            for binding in bindings
            if binding is not cls.probability_image_binding
        )

    @classmethod
    def postprocess_bound_settings(
        cls, module: ModuleBlock, bound: BoundModuleSettings
    ) -> BoundModuleSettings:
        """Bind the model and the tiling as each layout of the plugin writes them."""

        models = tuple(
            setting.value.strip()
            for setting in module.iter_settings()
            if setting_name_matches(setting.name, cls.model_setting)
        )
        kind = cls.setting_value(module, cls.model_kind_setting)
        if kind is None:
            # Nine rows: ``Model`` is the kind and no pretrained model is named.
            (kind,), models = models, ()
        kwargs: dict[str, object] = {}
        if kind in _MODEL_KINDS:
            kwargs["model_dimensions"] = kind
            if models:
                kwargs["pretrained_model"] = models[_MODEL_KINDS.index(kind)]
        else:
            _folder, _bar, directory = (
                cls.setting_value(module, cls.model_folder_setting) or ""
            ).partition("|")
            kwargs["model_folder"] = directory
        if cellprofiler_binary(cls.setting_value(module, cls.tile_setting) or "No"):
            kwargs["n_tiles"] = tuple(
                parse_cellprofiler_int(cls.setting_value(module, setting) or "1")
                for setting in (
                    cls.horizontal_tiles_setting,
                    cls.vertical_tiles_setting,
                )
            )
        return bound.with_kwargs(kwargs)


@runtime_image_execution_mode(FullStackExecution)
@numpy(contract=FlexibleContract)
def run_stardist(
    image: ImagePayload,
    model_dimensions: str | None = None,
    pretrained_model: str | None = None,
    model_folder: str | None = None,
    prob_thresh: float | None = None,
    nms_thresh: float | None = None,
    n_tiles: tuple[int, int] | None = None,
    save_probability_image: bool = False,
) -> tuple[ImagePayload, DataclassMeasurementColumnarRows, ObjectLabelValue]:
    """Segment star-convex objects with StarDist, as CellProfiler's RunStarDist does.

    Not runnable in this version of OpenHCS. ``prob_thresh``, ``nms_thresh`` and
    ``n_tiles`` are arguments of StarDist's ``predict_instances``.

    Args:
        model_dimensions: ``2D`` or ``3D`` for a pretrained model; unset for a
            model folder, whose model decides.
        pretrained_model: Name of a StarDist pretrained model. Unset when the
            pipeline was written by a plugin version that had no model choice.
        model_folder: Folder of a custom-trained model, as written in the
            pipeline.
        prob_thresh: Object probability threshold; unset uses the model's own.
        nms_thresh: Overlap threshold of non-maximum suppression; unset uses
            the model's own.
        n_tiles: Number of horizontal and vertical tiles the image is predicted
            in; unset predicts it whole.
        save_probability_image: Return StarDist's object probability, resized
            to the image, as the named image.
    """
    RunStarDistModule.cannot_run()
