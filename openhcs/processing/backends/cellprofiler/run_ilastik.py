"""CellProfiler plugin Runilastik.

Upstream: CellProfiler-plugins ``active_plugins/runilastik.py`` (settings
revision 1 at commit 5aaa4e5).

The plugin writes the image to an HDF5 file, runs the ilastik program on it
with a trained project, and reads the probabilities back. ilastik is a program,
not a Python distribution (PyPI has none), so this file requires no
distribution. OpenHCS has no function that runs an external program on a
step's images, so the step converts and cannot run.
"""

from typing import ClassVar

from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.core.callable_contract import runtime_image_execution_mode
from openhcs.core.image_payload_execution_mode import FullStackExecution
from openhcs.core.memory.decorators import numpy
from openhcs.core.processing_contracts import FlexibleContract
from openhcs.core.runtime_image_values import ImagePayload
from openhcs.interop.cellprofiler.module_without_function import (
    ModuleWithoutFunction,
)
from openhcs.interop.cellprofiler.setting_names import SettingNameFamily
from openhcs.interop.cellprofiler.settings_binder import SettingToKeywordBinding


class RunilastikModule(ModuleWithoutFunction):
    module_name = "Runilastik"
    function_name = "run_ilastik"
    what_openhcs_lacks = (
        "OpenHCS has no function that runs the ilastik program on a step's "
        "images with a trained project file."
    )
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input("Select the input image", ImageArtifactType),
        SettingToKeywordBinding.output("Name the output image", ImageArtifactType),
        SettingToKeywordBinding("Executable", "executable", str),
        SettingToKeywordBinding("Project file", "project_file", str),
        SettingToKeywordBinding("Select the project type", "project_type", str),
    )
    ignored_settings = (
        # Whether the plugin starts ilastik directly or inside a container.
        SettingNameFamily(
            "Run ilastik in a container (Docker or Podman) or local environment",
            aliases=("Run ilastik in docker or local environment",),
        ),
    )


@runtime_image_execution_mode(FullStackExecution)
@numpy(contract=FlexibleContract)
def run_ilastik(
    image: ImagePayload,
    executable: str | None = None,
    project_file: str | None = None,
    project_type: str = "Pixel Classification",
) -> ImagePayload:
    """Classify pixels with a trained ilastik project, as CellProfiler's Runilastik does.

    Not runnable in this version of OpenHCS.

    Args:
        executable: Path of the ilastik program, as written in the pipeline.
        project_file: Path of the trained ilastik project (``.ilp``), as written
            in the pipeline.
        project_type: ``Pixel Classification`` exports the probabilities;
            ``Autocontext (2-stage)`` exports the second stage's.
    """
    RunilastikModule.cannot_run()
