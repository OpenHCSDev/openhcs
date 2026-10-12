"""RunCellpose, RunStarDist and Runilastik convert; none can run yet.

Each block marked *written by the plugin* is copied from a pipeline someone
saved, with its repository, path and blob or commit. A block marked *built from
the plugin source* has the rows of that revision's ``settings()`` in order,
reconstructed from ``upgrade_settings`` of CellProfiler-plugins
``active_plugins/runcellpose.py`` at commit 5aaa4e5, because no saved pipeline
of that revision was found (GitHub code search, 2026-10-12: revisions 3 to 6).
"""

from __future__ import annotations

import inspect
import json
from dataclasses import dataclass
from pathlib import Path

import pytest

from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.pipeline.funcstep_contract_validator import (
    FuncStepContractValidator,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.module_settings import UnmappedModuleSettingsError
from openhcs.processing.backends.cellprofiler.run_cellpose import (
    RunCellposeModule,
    run_cellpose,
)
from openhcs.processing.backends.cellprofiler.run_ilastik import RunilastikModule
from openhcs.processing.backends.cellprofiler.run_stardist import RunStarDistModule
from openhcs.processing.backends.lib_registry import openhcs_registry
from tests.unit.test_cellprofiler_undeclared_and_unavailable_modules import (
    _compile_contracts,
    _import,
)

_REPOSITORY = Path(__file__).parents[2]
_PLUGINS = "CellProfiler/CellProfiler-plugins@5aaa4e5"
_TUTORIALS = "CellProfiler/tutorials"
_FOSSA = "broadinstitute/scripts_notebooks_fossa"


@dataclass(frozen=True)
class Block:
    """One module block, where it comes from and what it must convert to."""

    name: str
    source: str
    module: type[CellProfilerModule]
    text: str
    images: tuple[str, ...]
    """The images the block reads; the first is its input image."""
    arguments: dict[str, object]
    """Every keyword of the step's function: as written, or what an absent row means."""
    measured: str | None
    """The objects a following measurement module reads; ``None`` for an image."""

    @property
    def pipeline(self) -> str:
        assignments = "".join(
            f"""    Select the image type:Grayscale image
    Name to assign these images:{image}
    Select the rule criteria:and (file does contain "{image}")
"""
            for image in self.images
        )
        following = (
            f"""GaussianFilter:[module_num:3|variable_revision_number:1|enabled:True]
    Select the input image:{self.arguments["name_the_output_image"]}
    Name the output image:Smoothed
    Sigma:1
"""
            if self.measured is None
            else f"""MeasureObjectSizeShape:[module_num:3|variable_revision_number:3|enabled:True]
    Select object sets to measure:{self.measured}
    Calculate the Zernike features?:No
    Calculate the advanced features?:No
MeasureObjectIntensity:[module_num:4|variable_revision_number:4|enabled:True]
    Select images to measure:{self.images[0]}
    Select objects to measure:{self.measured}
"""
        )
        return (
            "CellProfiler Pipeline: https://cellprofiler.org\n"
            "NamesAndTypes:[module_num:1|enabled:True]\n"
            f"    Assignments count:{len(self.images)}\n"
            f"{assignments}{self.text}{following}"
        )


_CELLPOSE_ROW_ABSENT = {
    "model_type": None,
    "pretrained_model": None,
    "diameter": None,
    "anisotropy": None,
    "restore_type": None,
    "clip_to_percentiles": False,
    "remove_edge_objects": True,
    "anisotropy_from_voxel_spacing": True,
    "flow_threshold": 0.4,
    "cellprob_threshold": 0.0,
    "stitch_threshold": 0.0,
    "do_3D": False,
    "min_size": 15,
    "invert": False,
}
"""What RunCellpose's function is given for a row a revision does not have.

``upgrade_settings`` gives the same for the rows it adds, except edge removal,
which it never adds: revisions without the row get the plugin's default.
"""
_STARDIST_ROW_ABSENT = {
    "model_dimensions": None,
    "pretrained_model": None,
    "model_folder": None,
    "prob_thresh": None,
    "nms_thresh": None,
    "n_tiles": None,
}


def _cellpose(
    name: str, source: str, text: str, *images: str, **written: object
) -> Block:
    return Block(
        name,
        source,
        RunCellposeModule,
        text,
        images,
        {**_CELLPOSE_ROW_ABSENT, **written},
        written["name_the_output_object"],
    )


def _arguments(step) -> dict[str, object]:
    """The step's keywords over its function's defaults (a default is not stored)."""

    (invocation,) = normalize_function_pattern(step.func).iter_items()
    function = inspect.unwrap(invocation.contract.resolve_canonical_raw_callable())
    return {
        **{
            name: parameter.default
            for name, parameter in inspect.signature(function).parameters.items()
            if parameter.default is not parameter.empty
        },
        **invocation.kwargs_dict,
    }


_CELLPOSE_REVISION_3_TAIL = """    Use GPU:No
    Use averaging:Yes
    Supply nuclei image as well?:No
    Select the nuclei image:None
    Save probability image?:No
    Name the probability image:Probabilities
    Location of the pre-trained model file:Elsewhere...|
    Pre-trained model file name:cyto_0
    Flow threshold:0.4
    Cell probability threshold:0.0
    GPU memory share for each worker:0.1
    Stitch Threshold:0.0
    Use 3D:No
    Minimum size:10
"""

_BLOCKS = (
    _cellpose(
        "cellpose-r3-plugin-test-pipeline",
        f"written by the plugin: {_PLUGINS} "
        "tests/headless_test/4.2.5_plugins_test_pipeline_CELLPOSE.cppipe, module 5",
        """RunCellpose:[module_num:2|svn_version:'Unknown'|variable_revision_number:3|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Expected object diameter:12
    Detection mode:nuclei
    Name the output object:Nuclei_pose
"""
        + _CELLPOSE_REVISION_3_TAIL
        + """    Z rescaling factor (anisotropy):1.0
    Use Omnipose for mask reconstruction:No
    Invert images:No
""",
        "DNA",
        name_the_output_object="Nuclei_pose",
        cellpose_version="v2",
        model_type="nuclei",
        diameter=12.0,
        gpu=False,
        supply_nuclei_image=False,
        save_probability_image=False,
        flow_threshold=0.4,
        cellprob_threshold=0.0,
        stitch_threshold=0.0,
        do_3D=False,
        min_size=10,
        anisotropy=1.0,
        invert=False,
    ),
    _cellpose(
        "cellpose-r3-custom-model-and-probabilities",
        f"written by the plugin: {_FOSSA} "
        "cellprofiler/ToxPath_pipeline/analysis.cppipe "
        "(blob 591e5b820446f8024536f1e5aef0d39fed5ddd3b), module 5",
        """RunCellpose:[module_num:2|svn_version:'Unknown'|variable_revision_number:3|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Expected object diameter:60
    Detection mode:custom
    Name the output object:NucleiCP
    Use GPU:No
    Use averaging:Yes
    Supply nuclei image as well?:No
    Select the nuclei image:None
    Save probability image?:Yes
    Name the probability image:Probabilities
    Location of the pre-trained model file:Elsewhere...|/home/ubuntu/bucket/projects/2022_10_04_AgNPCellRecovery_fossa_Cimini/workspace/model/2022_05_30_ToxPath
    Pre-trained model file name:CP_20221130_102925
    Flow threshold:0.7
    Cell probability threshold:1
    GPU memory share for each worker:0.1
    Stitch Threshold:0.0
    Use 3D:No
    Minimum size:200
    Use Omnipose for mask reconstruction:1.0
    Invert images:No
""",
        "DNA",
        name_the_output_object="NucleiCP",
        cellpose_version="v2",
        pretrained_model=(
            "/home/ubuntu/bucket/projects/2022_10_04_AgNPCellRecovery_fossa_Cimini"
            "/workspace/model/2022_05_30_ToxPath/CP_20221130_102925"
        ),
        diameter=60.0,
        gpu=False,
        supply_nuclei_image=False,
        save_probability_image=True,
        name_the_probability_image="Probabilities",
        flow_threshold=0.7,
        cellprob_threshold=1.0,
        stitch_threshold=0.0,
        do_3D=False,
        min_size=200,
        invert=False,
    ),
    _cellpose(
        "cellpose-r3-edge-removal-row",
        f"written by the plugin: {_FOSSA} "
        "cellprofiler/mimic_nuclei_pipeline/MimicNuclei.cppipe "
        "(blob c95ca18ec02485cc2626761c433db0c3b69d137d), module 7",
        r"""RunCellpose:[module_num:2|svn_version:'Unknown'|variable_revision_number:3|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:LT
    Expected object diameter:148
    Detection mode:custom
    Name the output object:Cells
    Use GPU:No
    Use averaging:Yes
    Supply nuclei image as well?:No
    Select the nuclei image:None
    Save probability image?:Yes
    Name the probability image:Probabilities
    Location of the pre-trained model file:Elsewhere...|D:\\2022_09_09_LiveCellPainting_fossa_Cimini\\workspace\\model\\2022_03_24_Acidification_LT
    Pre-trained model file name:CP_20230327_164451
    Flow threshold:0.7
    Cell probability threshold:-4
    GPU memory share for each worker:0.1
    Stitch Threshold:0.0
    Use 3D:No
    Minimum size:30
    Use Omnipose for mask reconstruction:No
    Invert images:No
    Remove objects that are touching the edge?:Yes
""",
        "LT",
        name_the_output_object="Cells",
        cellpose_version="v2",
        pretrained_model=(
            r"D:\2022_09_09_LiveCellPainting_fossa_Cimini\workspace\model"
            r"\2022_03_24_Acidification_LT/CP_20230327_164451"
        ),
        diameter=148.0,
        gpu=False,
        supply_nuclei_image=False,
        save_probability_image=True,
        name_the_probability_image="Probabilities",
        flow_threshold=0.7,
        cellprob_threshold=-4.0,
        stitch_threshold=0.0,
        do_3D=False,
        min_size=30,
        invert=False,
        remove_edge_objects=True,
    ),
    _cellpose(
        "cellpose-r6-tutorial",
        f"written by the plugin: {_TUTORIALS} "
        "BeginnerSegmentation/bonus_materials/bonus_3_cellpose.cppipe "
        "(blob 6c6d98a26253c201b5a6ccc11f6379ec89a15cd0), module 5",
        """RunCellpose:[module_num:2|svn_version:'Unknown'|variable_revision_number:6|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:OrigDNA
    Rescale images before running Cellpose:No
    Run CellPose in docker or local python environment:Docker
    Select Cellpose docker image:cellprofiler/runcellpose_with_pretrained:2.3.2
    Expected object diameter:30
    Detection mode:nuclei
    Name the output object:RunCellpose
    Use GPU:No
    Use averaging:No
    Supply nuclei image as well?:No
    Select the nuclei image:None
    Save probability image?:No
    Name the probability image:Probabilities
    Location of the pre-trained model file:Elsewhere...|
    Pre-trained model file name:cyto_0
    Flow threshold:0.4
    Cell probability threshold:0.0
    GPU memory share for each worker:0.1
    Stitch Threshold:0.0
    Use 3D:No
    Minimum size:15
    Use Omnipose for mask reconstruction:No
    Invert images:No
    Remove objects that are touching the edge?:Yes
    Rescale probability map?:No
""",
        "OrigDNA",
        name_the_output_object="RunCellpose",
        cellpose_version="v2",
        model_type="nuclei",
        diameter=30.0,
        clip_to_percentiles=False,
        gpu=False,
        supply_nuclei_image=False,
        save_probability_image=False,
        flow_threshold=0.4,
        cellprob_threshold=0.0,
        stitch_threshold=0.0,
        do_3D=False,
        min_size=15,
        invert=False,
        remove_edge_objects=True,
    ),
    _cellpose(
        "cellpose-r1",
        "built from the plugin source: revision 1 rows",
        """RunCellpose:[module_num:2|variable_revision_number:1|enabled:True]
    Select the input image:Cyto
    Expected object diameter:0
    Detection mode:cyto
    Name the output object:Cells
    Use GPU:Yes
    Use averaging:Yes
    Supply nuclei image as well?:Yes
    Select the nuclei image:DNA
    Save probability image?:No
    Name the probability image:Probabilities
    Location of the pre-trained model file:Elsewhere...|
    Pre-trained model file name:cyto_0
""",
        "Cyto",
        "DNA",
        name_the_output_object="Cells",
        cellpose_version="v2",
        model_type="cyto",
        gpu=True,
        supply_nuclei_image=True,
        save_probability_image=False,
    ),
    _cellpose(
        "cellpose-r8-cellpose-3-with-restoration",
        "built from the plugin source: revision 8 rows of settings()",
        """RunCellpose:[module_num:2|variable_revision_number:8|enabled:True]
    Select the input image:DNA
    Rescale images before running Cellpose:Yes
    Run CellPose in a Docker/Podman container or local python environment:Python
    Select Cellpose version:v3
    Select Cellpose docker image:cellprofiler/runcellpose_omnipose_no_pretrained:1.0.2
    Select Cellpose docker image:cellprofiler/runcellpose_no_pretrained:2.3.2
    Select Cellpose docker image:cellprofiler/runcellpose_with_pretrained:3.1.1.2
    Select Cellpose docker image:cellprofiler/runcellpose_with_pretrained:4.0.6
    Specify expected object diameter?:No
    Expected object diameter:17
    Detection mode:cyto
    Detection mode:cyto2
    Detection mode:tissuenet_cp3
    Detection mode:cpsam
    Name the output object:Nuclei
    Use GPU:No
    Use averaging:No
    Supply nuclei image as well?:No
    Select the nuclei image:None
    Save probability image?:No
    Name the probability image:Probabilities
    Location of the pre-trained model file:Default Input Folder|
    Pre-trained model file name:cyto_0
    Flow threshold:0.4
    Cell probability threshold:0.0
    GPU memory share for each worker:0.1
    Stitch Threshold:0.25
    Use 3D:Yes
    Minimum size:15
    Use Omnipose for mask reconstruction:No
    Invert images:Yes
    Remove objects that are touching the edge?:No
    Rescale probability map?:Yes
    Preprocess image before segmentation?:Yes
    Preprocessing model:denoise_nuclei
    Save preprocessed image?:No
    Name the preprocessed image:Preprocessed
    Cache model between image sets:No
    Rescale for anisotropy?:No
""",
        "DNA",
        name_the_output_object="Nuclei",
        cellpose_version="v3",
        model_type="tissuenet_cp3",
        diameter=17.0,
        restore_type="denoise_nuclei",
        clip_to_percentiles=True,
        gpu=False,
        supply_nuclei_image=False,
        save_probability_image=False,
        flow_threshold=0.4,
        cellprob_threshold=0.0,
        stitch_threshold=0.25,
        do_3D=True,
        min_size=15,
        invert=True,
        remove_edge_objects=False,
        anisotropy_from_voxel_spacing=False,
    ),
    Block(
        "stardist-nine-rows-plugin-test-pipeline",
        f"written by the plugin: {_PLUGINS} "
        "tests/headless_test/4.2.5_plugins_test_pipeline_STARDIST.cppipe, module 5",
        RunStarDistModule,
        """RunStarDist:[module_num:2|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Model:2D
    Name the output object:RunStarDist
    Tile input image?:No
    Horizontal tiles:1
    Vertical tiles:1
    Save probability image?:Yes
    Name the probability image:Probabilities
    Model folder:Elsewhere...|
""",
        ("DNA",),
        {
            **_STARDIST_ROW_ABSENT,
            "name_the_output_object": "RunStarDist",
            "model_dimensions": "2D",
            "save_probability_image": True,
            "name_the_probability_image": "Probabilities",
        },
        "RunStarDist",
    ),
    Block(
        "stardist-nine-rows-custom-model",
        f"written by the plugin: {_TUTORIALS} Deprecated_Tutorials/"
        "Plugins_runCellpose_runStarDist/runCellpose_runStarDist_tutorial_materials/"
        "Blastoid (Stardist 3D)/blastoid_3D-Stardist.cppipe "
        "(blob a51ccbb88aa1d665e02b4c4bce7fd5e1654a5fd1), module 6",
        RunStarDistModule,
        """RunStarDist:[module_num:2|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:Resize
    Model:Custom
    Name the output object:RunStarDist
    Tile input image?:No
    Horizontal tiles:1
    Vertical tiles:1
    Save probability image?:Yes
    Name the probability image:Probabilities
    Model folder:Elsewhere...|/Users/bdiazroh/Documents/GitHub/stardist/models/examples/3D_demo
""",
        ("Resize",),
        {
            **_STARDIST_ROW_ABSENT,
            "name_the_output_object": "RunStarDist",
            "model_folder": (
                "/Users/bdiazroh/Documents/GitHub/stardist/models/examples/3D_demo"
            ),
            "save_probability_image": True,
            "name_the_probability_image": "Probabilities",
        },
        "RunStarDist",
    ),
    Block(
        "stardist-fifteen-rows",
        "built from the plugin source: rows of settings() at 5aaa4e5",
        RunStarDistModule,
        """RunStarDist:[module_num:2|variable_revision_number:1|enabled:True]
    Select the input image:DNA
    Model Type:3D
    Name the output object:Nuclei
    Tile input image?:Yes
    Horizontal tiles:2
    Vertical tiles:3
    Save probability image?:No
    Name the probability image:Probabilities
    Model folder:Default Input Folder|
    Model:Versatile (fluorescent nuclei)
    Model:3D_demo
    Probability threshold:0.5
    Overlap threshold:0.4
    Manually set how much GPU memory each worker can use?:No
    GPU memory (in GB) for each worker:0.5
""",
        ("DNA",),
        {
            **_STARDIST_ROW_ABSENT,
            "name_the_output_object": "Nuclei",
            "model_dimensions": "3D",
            "pretrained_model": "3D_demo",
            "n_tiles": (2, 3),
            "prob_thresh": 0.5,
            "nms_thresh": 0.4,
            "save_probability_image": False,
        },
        "Nuclei",
    ),
    Block(
        "ilastik-tutorial",
        f"written by the plugin: {_TUTORIALS} "
        "BeginnerSegmentation/bonus_materials/bonus_2_ilastik.cppipe "
        "(blob e474095d4b2e3da38d6f836f89355ceb6cd243b5), module 11",
        RunilastikModule,
        """Runilastik:[module_num:2|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:OrigRNA
    Name the output image:Runilastik
    Run ilastik in docker or local environment:Local
    Executable:
    Project file:
    Select the project type:Pixel Classification
""",
        ("OrigRNA",),
        {
            "executable": None,
            "project_file": None,
            "name_the_output_image": "Runilastik",
            "project_type": "Pixel Classification",
        },
        None,
    ),
)
_REQUIRING_A_DISTRIBUTION = {RunCellposeModule: "cellpose", RunStarDistModule: "stardist"}

blocks = pytest.mark.parametrize("block", _BLOCKS, ids=lambda block: block.name)


@blocks
def test_block_converts_to_its_declared_step_feeding_the_next_module(
    tmp_path: Path, block: Block
) -> None:
    steps, _pipeline_config = _import(tmp_path, block.pipeline)

    assert steps[0].name == block.module.require_module_name()
    (invocation,) = normalize_function_pattern(steps[0].func).iter_items()
    assert (
        CellProfilerModule.require_callable_contract_owner(invocation.contract)
        is block.module
    )
    assert _arguments(steps[0]) == block.arguments
    assert [step.name for step in steps[1:]] == (
        ["GaussianFilter"]
        if block.measured is None
        else ["MeasureObjectSizeShape", "MeasureObjectIntensity"]
    )


@blocks
def test_compiling_is_refused_with_the_install_command_then_with_what_is_lacking(
    tmp_path: Path, monkeypatch, block: Block
) -> None:
    steps, pipeline_config = _import(tmp_path, block.pipeline)
    (invocation,) = normalize_function_pattern(steps[0].func).iter_items()
    distribution = _REQUIRING_A_DISTRIBUTION.get(block.module)

    if distribution is not None:
        # The later modules' contracts compile against this step's outputs.
        assert _compile_contracts(steps, pipeline_config) is not None
        with pytest.raises(ValueError) as not_installed:
            FuncStepContractValidator.validate_external_library_installation(
                invocation.contract.func, steps[0].name
            )
        assert (
            f"Function '{invocation.contract.function_name}' in step "
            f"'{steps[0].name}' requires external library '{distribution}' which "
            "is not installed."
        ) in str(not_installed.value)
        assert f"Install with: pip install 'openhcs[{distribution}]'" in str(
            not_installed.value
        )
        monkeypatch.setattr(openhcs_registry, "_distribution_installed", lambda _: True)

    FuncStepContractValidator.validate_external_library_installation(
        invocation.contract.func, steps[0].name
    )
    with pytest.raises(ValueError) as lacking:
        _compile_contracts(steps, pipeline_config)
    assert str(lacking.value).endswith(block.module.cannot_run_message())
    assert block.module.what_openhcs_lacks in str(lacking.value)
    with pytest.raises(NotImplementedError) as called:
        inspect.unwrap(invocation.contract.resolve_canonical_raw_callable())(None)
    assert str(called.value) == block.module.cannot_run_message()


def test_a_row_no_revision_of_the_plugin_writes_is_not_silently_dropped(
    tmp_path: Path,
) -> None:
    block = _BLOCKS[0]

    with pytest.raises(UnmappedModuleSettingsError, match="a_setting_of_the_future"):
        _import(
            tmp_path,
            block.pipeline.replace(
                "    Invert images:No\n",
                "    Invert images:No\n    A setting of the future:1\n",
            ),
        )


def test_cellpose_keywords_are_parameters_of_the_recorded_cellpose_functions() -> None:
    """Checked against the functions' signatures recorded from their branch."""

    recorded = json.loads(
        (
            _REPOSITORY
            / "tests/fixtures/cellprofiler_plugins/cellpose_functions_signature.json"
        ).read_text()
    )
    assert recorded["branch"] == "feature/cellpose-full-surface"
    assert recorded["module"] in RunCellposeModule.what_openhcs_lacks
    functions = recorded["functions"]
    segment = functions["segment"]["parameters"]
    around_the_model = {
        "cellpose_version",
        "anisotropy_from_voxel_spacing",
        "clip_to_percentiles",
        "remove_edge_objects",
        "supply_nuclei_image",
        "save_probability_image",
    }
    parameters = dict(inspect.signature(inspect.unwrap(run_cellpose)).parameters)
    del parameters["image"]

    of_the_functions = set(parameters) - around_the_model
    assert of_the_functions - {"restore_type"} <= set(segment)
    assert "restore_type" in functions["restore_and_segment"]["parameters"]
    assert around_the_model.isdisjoint(
        name for function in functions.values() for name in function["parameters"]
    )
    # A name is a model's value in the recorded enums; a file is a path.
    as_recorded = {"model_type": "None", "pretrained_model": "None"}
    assert {
        name: repr(parameters[name].default)
        for name in of_the_functions - {"restore_type"}
    } == {
        name: as_recorded.get(name, segment[name]["default"])
        for name in of_the_functions - {"restore_type"}
    }
    # Every function the module names is recorded, with the objects it returns.
    for name in ("segment", "segment_estimating_diameter", "restore_and_segment"):
        assert name in RunCellposeModule.what_openhcs_lacks
        assert ["labels", "ObjectLabelsArtifactType"] in functions[name]["outputs"]
        assert ["cell_probability", "ImageArtifactType"] in functions[name]["outputs"]
    # Model names the blocks use that the recorded Cellpose 3 has.
    models = set(recorded["enums"]["SegmentationModel"].values())
    assert {"nuclei", "cyto", "tissuenet_cp3"} <= models
    assert "denoise_nuclei" in recorded["enums"]["RestorationModel"].values()
