"""CellProfiler plugin RunCellpose.

Upstream: CellProfiler-plugins ``active_plugins/runcellpose.py`` (settings
revision 8 at commit 5aaa4e5; every earlier revision's rows are declared too).

The module's keywords are the parameters of OpenHCS's Cellpose functions
(``openhcs.processing.backends.lib_registry.derived.cellpose`` on branch
``feature/cellpose-full-surface``), plus the few things RunCellpose does around
the model. Those functions are not in this version of OpenHCS, so the step
converts and cannot run.

CellProfiler writes each setting's label beside its value, and settings bind by
label here. That covers every layout the plugin has had, including the ones it
changed without raising its revision number (revision 3 exists with and
without ``Z rescaling factor (anisotropy)`` and ``Remove objects that are
touching the edge?``).
"""

from typing import TYPE_CHECKING, ClassVar

from openhcs.core.artifacts.kinds import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.artifacts.relations import SourceStackLineageSourceRelation
from openhcs.core.artifacts.specs import ArtifactSpecCollection
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
from openhcs.interop.cellprofiler.setting_names import (
    SettingNameFamily,
    setting_name_matches,
)
from openhcs.interop.cellprofiler.settings_binder import (
    ModuleOnlySettingBinding,
    SettingToKeywordBinding,
    parse_cellprofiler_float,
    parse_cellprofiler_int,
)

if TYPE_CHECKING:
    from openhcs.core.function_patterns import FunctionInvocationKey
    from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext

REQUIRED_DISTRIBUTIONS = ("cellpose",)

_CELLPOSE_VERSIONS = ("omnipose", "v2", "v3", "v4")
"""The plugin's ``Select Cellpose version`` choices, in the order of its rows.

From revision 7 the plugin writes one ``Detection mode`` row for each of them,
in this order, and reads the row of the selected version.
"""


class RunCellposeModule(
    MeasurementArtifactOutputModule,
    ObjectArtifactOutputModule,
    ModuleWithoutFunction,
):
    module_name = "RunCellpose"
    function_name = "run_cellpose"
    what_openhcs_lacks = (
        "it runs through OpenHCS's Cellpose functions (segment, "
        "segment_estimating_diameter and restore_and_segment of "
        "openhcs.processing.backends.lib_registry.derived.cellpose), which this "
        "version of OpenHCS does not have."
    )

    version_setting = "Select Cellpose version"
    version_before_the_setting_existed = "v2"
    """What the plugin's upgrade gives a pipeline written before revision 7."""
    mode_setting = "Detection mode"
    custom_mode = "custom"
    specify_diameter_setting = "Specify expected object diameter?"
    diameter_setting = "Expected object diameter"
    model_directory_setting = "Location of the pre-trained model file"
    model_file_setting = "Pre-trained model file name"
    restore_setting = "Preprocess image before segmentation?"
    restore_model_setting = "Preprocessing model"
    supply_nuclei_setting = "Supply nuclei image as well?"
    save_probability_setting = "Save probability image?"

    input_image_binding = SettingToKeywordBinding.input(
        "Select the input image", ImageArtifactType
    )
    nuclei_image_binding = SettingToKeywordBinding.input(
        "Select the nuclei image",
        ImageArtifactType,
    )
    probability_image_binding = SettingToKeywordBinding.output(
        "Name the probability image", ImageArtifactType
    )
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        input_image_binding,
        SettingToKeywordBinding.output(
            "Name the output object", ObjectLabelsArtifactType
        ),
        SettingToKeywordBinding(
            supply_nuclei_setting, "supply_nuclei_image", cellprofiler_binary
        ),
        nuclei_image_binding,
        SettingToKeywordBinding(
            save_probability_setting, "save_probability_image", cellprofiler_binary
        ),
        probability_image_binding,
        SettingToKeywordBinding("Use GPU", "gpu", cellprofiler_binary),
        SettingToKeywordBinding(
            "Flow threshold", "flow_threshold", parse_cellprofiler_float
        ),
        SettingToKeywordBinding(
            "Cell probability threshold", "cellprob_threshold", parse_cellprofiler_float
        ),
        SettingToKeywordBinding(
            "Stitch Threshold", "stitch_threshold", parse_cellprofiler_float
        ),
        SettingToKeywordBinding("Use 3D", "do_3D", cellprofiler_binary),
        SettingToKeywordBinding("Minimum size", "min_size", parse_cellprofiler_int),
        SettingToKeywordBinding("Invert images", "invert", cellprofiler_binary),
        SettingToKeywordBinding(
            "Z rescaling factor (anisotropy)", "anisotropy", parse_cellprofiler_float
        ),
        SettingToKeywordBinding(
            "Rescale for anisotropy?",
            "anisotropy_from_voxel_spacing",
            cellprofiler_binary,
        ),
        SettingToKeywordBinding(
            "Rescale images before running Cellpose",
            "clip_to_percentiles",
            cellprofiler_binary,
        ),
        SettingToKeywordBinding(
            "Remove objects that are touching the edge?",
            "remove_edge_objects",
            cellprofiler_binary,
        ),
        # Read together in ``postprocess_bound_settings``.
        ModuleOnlySettingBinding(version_setting),
        ModuleOnlySettingBinding(mode_setting),
        ModuleOnlySettingBinding(specify_diameter_setting),
        ModuleOnlySettingBinding(diameter_setting),
        ModuleOnlySettingBinding(model_directory_setting),
        ModuleOnlySettingBinding(model_file_setting),
        ModuleOnlySettingBinding(restore_setting),
        ModuleOnlySettingBinding(restore_model_setting),
    )
    ignored_settings = (
        # Where the plugin runs Cellpose. OpenHCS calls Cellpose in its own
        # process; the version the pipeline asks for is ``cellpose_version``.
        SettingNameFamily(
            "Run CellPose in a Docker/Podman container or local python environment",
            aliases=("Run CellPose in docker or local python environment",),
        ),
        "Select Cellpose docker image",
        # Cellpose 3 has no network averaging (``net_avg`` ended with 2.x).
        "Use averaging",
        # A share of GPU memory is process state; device assignment owns it.
        "GPU memory share for each worker",
        # Passed only by the plugin's Omnipose path, which ``cellpose_version``
        # already names.
        "Use Omnipose for mask reconstruction",
        # Written by the plugin and never read by its ``run``.
        "Rescale probability map?",
        # The plugin shows the restored image in its window and never saves it.
        "Save preprocessed image?",
        "Name the preprocessed image",
        # OpenHCS keeps one model per set of constructor arguments per process.
        "Cache model between image sets",
    )

    @classmethod
    def active_artifact_bindings(
        cls,
        module: ModuleBlock | None,
        *,
        invocation_key: "FunctionInvocationKey | None" = None,
    ) -> tuple[SettingToKeywordBinding, ...]:
        """The second image and the probability image exist only when asked for."""

        bindings = super().active_artifact_bindings(
            module, invocation_key=invocation_key
        )
        if module is None:
            return bindings
        inactive = tuple(
            binding
            for binding, asked_by in (
                (cls.nuclei_image_binding, cls.supply_nuclei_setting),
                (cls.probability_image_binding, cls.save_probability_setting),
            )
            if not cellprofiler_binary(cls.setting_value(module, asked_by) or "No")
        )
        return tuple(binding for binding in bindings if binding not in inactive)

    @classmethod
    def artifact_output_relations(
        cls,
        module: ModuleBlock,
        *,
        binding: SettingToKeywordBinding,
        name: str,
        invocation_key: "FunctionInvocationKey",
        step_context: "ArtifactDeclarationStepContext",
        artifact_inputs: ArtifactSpecCollection,
        output_position: int,
    ) -> tuple[SourceStackLineageSourceRelation, ...]:
        """The objects and the probability image lie on the input image.

        With a nuclei image the step reads two images, and neither output is
        of the nuclei image.
        """

        del binding, name, invocation_key, step_context, output_position
        (input_image,) = cls.artifact_names_for_binding(module, cls.input_image_binding)
        return (
            SourceStackLineageSourceRelation(
                source=artifact_inputs.require_by_name_and_artifact_type(
                    input_image, ImageArtifactType
                ).ref()
            ),
        )

    @classmethod
    def _rows(cls, module: ModuleBlock, setting_name: str) -> tuple[str, ...]:
        """Return every value written under one label, in file order."""

        return tuple(
            setting.value.strip()
            for setting in module.iter_settings()
            if setting_name_matches(setting.name, setting_name)
        )

    @classmethod
    def postprocess_bound_settings(
        cls, module: ModuleBlock, bound: BoundModuleSettings
    ) -> BoundModuleSettings:
        """Bind the model, the diameter and the restoration as the plugin reads them."""

        (version,) = cls._rows(module, cls.version_setting) or (
            cls.version_before_the_setting_existed,
        )
        modes = cls._rows(module, cls.mode_setting)
        mode = modes[_CELLPOSE_VERSIONS.index(version)] if len(modes) > 1 else modes[0]
        kwargs: dict[str, object] = {"cellpose_version": version}
        if mode == cls.custom_mode:
            _folder, _bar, directory = (
                cls.setting_value(module, cls.model_directory_setting) or ""
            ).partition("|")
            file_name = cls.setting_value(module, cls.model_file_setting) or ""
            kwargs["pretrained_model"] = "/".join(
                part for part in (directory.rstrip("/\\"), file_name) if part
            )
        else:
            kwargs["model_type"] = mode
        # Cellpose 4 takes a diameter only when the pipeline says to; earlier
        # versions estimate it when the pipeline gives zero.
        diameter = parse_cellprofiler_float(
            cls.setting_value(module, cls.diameter_setting) or "0"
        )
        specified = version != "v4" or cellprofiler_binary(
            cls.setting_value(module, cls.specify_diameter_setting) or "No"
        )
        if specified and diameter > 0:
            kwargs["diameter"] = diameter
        # The plugin restores only with Cellpose 3.
        if version == "v3" and cellprofiler_binary(
            cls.setting_value(module, cls.restore_setting) or "No"
        ):
            kwargs["restore_type"] = cls.setting_value(
                module, cls.restore_model_setting
            )
        return bound.with_kwargs(kwargs)


@runtime_image_execution_mode(FullStackExecution)
@numpy(contract=FlexibleContract)
def run_cellpose(
    image: ImagePayload,
    cellpose_version: str = "v3",
    model_type: str | None = None,
    pretrained_model: str | None = None,
    gpu: bool = False,
    diameter: float | None = None,
    flow_threshold: float = 0.4,
    cellprob_threshold: float = 0.0,
    stitch_threshold: float = 0.0,
    do_3D: bool = False,
    min_size: int = 15,
    invert: bool = False,
    anisotropy: float | None = None,
    restore_type: str | None = None,
    anisotropy_from_voxel_spacing: bool = True,
    clip_to_percentiles: bool = False,
    remove_edge_objects: bool = True,
    supply_nuclei_image: bool = False,
    save_probability_image: bool = False,
) -> tuple[ImagePayload, DataclassMeasurementColumnarRows, ObjectLabelValue]:
    """Segment objects with Cellpose, as CellProfiler's RunCellpose plugin does.

    Not runnable in this version of OpenHCS. ``model_type``, ``pretrained_model``,
    ``gpu``, ``diameter``, ``flow_threshold``, ``cellprob_threshold``,
    ``stitch_threshold``, ``do_3D``, ``min_size``, ``invert``, ``anisotropy`` and
    ``restore_type`` are parameters of OpenHCS's Cellpose functions and mean what
    Cellpose documents.

    Args:
        cellpose_version: Cellpose line the pipeline was written for
            (``omnipose``, ``v2``, ``v3`` or ``v4``). Model names differ between
            lines.
        model_type: Name of a Cellpose pretrained model.
        pretrained_model: A custom model file, used instead of ``model_type``.
        diameter: Expected object diameter in pixels; unset lets Cellpose
            estimate it.
        restore_type: Name of a Cellpose restoration model run on the image
            before segmentation; unset segments the image as it is.
        anisotropy_from_voxel_spacing: For 3D, take ``anisotropy`` from the
            image's plane spacing divided by its pixel size when it is unset.
        clip_to_percentiles: Scale the image so its 1st and 99th percentiles
            become 0 and 1, and clip, before Cellpose sees it.
        remove_edge_objects: Discard objects touching the image border. The
            plugin does this when it runs Cellpose in a container or runs
            Cellpose 4.
        supply_nuclei_image: The step's images are the input image and a nuclei
            image; Cellpose is given the second as its nuclear channel unless
            the model is ``nuclei``.
        save_probability_image: Return Cellpose's cell probability, scaled
            between its 1st and 99th percentiles, as the named image.
    """
    RunCellposeModule.cannot_run()
