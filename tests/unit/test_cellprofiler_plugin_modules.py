"""CellProfiler plugin modules reproduce the plugins themselves.

``tests/fixtures/cellprofiler_plugins`` holds a pipeline of plugin blocks
(``cases.cppipe``) and what the real plugins, run by CellProfiler 4.2.8.1,
stored for each block (``reference.npz``; versions, plugin commit and the blocks
the plugin itself fails on are in ``reference.json``). ``make_reference.py``
there regenerates both. The same blocks are bound and executed here.
"""

from __future__ import annotations

import inspect
import json
from dataclasses import replace
from pathlib import Path

import numpy as np
import pytest

from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.core.artifacts.plans import ArtifactInputPlan, ArtifactOutputPlan
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.runtime_image_values import ImagePayload, ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import NoPlaneAxis, RuntimeSlicePlaneAxis
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    VolumeSourceSpatialDomain,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.parser import CPPipeParser, ModuleBlock
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.interop.cellprofiler.settings_binder import SettingsBinder

_FIXTURES = Path(__file__).parents[1] / "fixtures" / "cellprofiler_plugins"
_REFERENCE = np.load(_FIXTURES / "reference.npz")
_REFERENCE_FACTS = json.loads((_FIXTURES / "reference.json").read_text())
_PLUGIN_RAISED = _REFERENCE_FACTS["plugin_raised"]
# scikit-image 0.26 against CellProfiler's 0.18.3: global equalization differs by
# up to 4.2e-7 (float32 rounding); every other case is bit-identical.
_TOLERANCE = 1e-6


def _artifact_names(
    block: ModuleBlock, plan_type: type[ArtifactInputPlan | ArtifactOutputPlan]
) -> dict[str | None, tuple[str, ...]]:
    """Image names a block declares, keyed by the function parameter they feed."""
    module_type = CellProfilerModule.require_module(block.name)
    declared = {}
    for binding in module_type.artifact_bindings_for(block, plan_type=plan_type):
        assert binding.require_artifact_type() is ImageArtifactType
        declared[binding.runtime_parameter_name] = (
            module_type.artifact_names_for_binding(block, binding)
        )
    return declared


def _output_name(block: ModuleBlock) -> str:
    ((name,),) = _artifact_names(block, ArtifactOutputPlan).values()
    return name


_CASES = {
    _output_name(block): block
    for block in CPPipeParser().parse(_FIXTURES / "cases.cppipe")
}


def _image(pixels: np.ndarray, *, volume: bool, stacked: bool = False) -> ImagePayload:
    return ImagePayloadMetadata(
        source_voxel_spacing=SourceVoxelSpacing(
            values_zyx=_REFERENCE_FACTS["voxel_spacing_zyx_of_volumes"] if volume else ()
        ),
        source_spatial_domain=(
            VolumeSourceSpatialDomain() if volume else SourceSpatialDomain()
        ),
        plane_axis=RuntimeSlicePlaneAxis if stacked else NoPlaneAxis,
    ).payload_with(pixels, None)


def _execute(block: ModuleBlock, image: ImagePayload) -> np.ndarray:
    """Bind the block's settings and run its function the way the runtime does."""
    module_type = CellProfilerModule.require_module(block.name)
    contract = replace(
        CallableContract.from_callable(
            module_type.require_callable()
        ).with_prepared_signature(),
        runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
    )
    image_names = module_type.compile_time_parameter_names(contract)
    kwargs = {
        name: value
        for name, value in module_type.bind_settings(
            block, binder=SettingsBinder()
        ).kwargs.items()
        if name not in image_names
    }
    for parameter, names in _artifact_names(block, ArtifactInputPlan).items():
        if parameter is not None and names:
            (name,) = names
            kwargs[parameter] = _REFERENCE[f"input_{name}"]
    return CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        image,
        kwargs,
        execution_mode=contract.runtime_image_execution_mode,
    ).data


def _input_pixels(block: ModuleBlock) -> np.ndarray:
    (name,) = _artifact_names(block, ArtifactInputPlan)[None]
    return _REFERENCE[f"input_{name}"]


@pytest.mark.parametrize("output_name", sorted(_CASES))
def test_output_equals_what_the_plugin_stored(output_name: str) -> None:
    block = _CASES[output_name]
    pixels = _input_pixels(block)
    image = _image(pixels, volume=pixels.ndim == 3)

    if output_name in _PLUGIN_RAISED:
        with pytest.raises(ValueError, match="the CellProfiler plugin fails"):
            _execute(block, image)
        return

    expected = _REFERENCE[f"output_{output_name}"]
    actual = _execute(block, image)
    assert actual.dtype == expected.dtype == np.float32
    np.testing.assert_allclose(actual, expected, rtol=0, atol=_TOLERANCE)


@pytest.mark.parametrize(
    "output_name",
    ("EqualizedPlaneWithinMask", "RescaledPlaneDistance", "PlaneMatchedToReference"),
)
def test_each_image_of_a_stack_is_processed_on_its_own(output_name: str) -> None:
    block = _CASES[output_name]
    pixels = _input_pixels(block)
    other = np.ascontiguousarray(pixels[::-1, ::-1])

    stacked = _execute(
        block, _image(np.stack((pixels, other)), volume=False, stacked=True)
    )

    np.testing.assert_array_equal(
        stacked,
        np.stack(
            [_execute(block, _image(one, volume=False)) for one in (pixels, other)]
        ),
    )


@pytest.mark.parametrize(
    ("output_name", "inputs"),
    (
        ("EqualizedPlane", {None: ("Plane",), "mask_image": ()}),
        (
            "EqualizedPlaneWithinMask",
            {None: ("Plane",), "mask_image": ("MaskPlane",)},
        ),
        ("PlaneDistance", {None: ("BinaryPlane",)}),
        (
            "PlaneMatchedToReference",
            {None: ("Plane",), "reference": ("ReferencePlane",)},
        ),
        # CellProfiler's blank value names no image.
        ("VolumeMatchedToFrame", {None: ("Volume",), "reference": ()}),
    ),
)
def test_block_declares_its_input_images_and_one_output_image(
    output_name: str, inputs: dict[str | None, tuple[str, ...]]
) -> None:
    block = _CASES[output_name]

    assert _artifact_names(block, ArtifactInputPlan) == inputs
    assert _artifact_names(block, ArtifactOutputPlan) == {None: (output_name,)}


_SOURCE = """CellProfiler Pipeline: http://www.cellprofiler.org
NamesAndTypes:[module_num:1|enabled:True]
    Assignments count:1
    Select the image type:Grayscale image
    Name to assign these images:{image}
    Select the rule criteria:and (file does contain "{image}")
"""

# Blocks below are verbatim from pipelines found in the wild, apart from the one
# noted change. They carry both spellings of the 3D setting and a fork's extra
# setting.

# CellProfiler/CellProfiler-plugins tests/headless_test/4.2.5_plugins_test_pipeline_BASIC.cppipe
_PLUGINS_TEST_PIPELINE = (
    _SOURCE.format(image="DNA")
    + """DistanceTransform:[module_num:7|svn_version:'Unknown'|variable_revision_number:1|show_window:True|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Name the output image:DistanceTransform
    Rescale values from 0 to 1?:Yes

HistogramEqualization:[module_num:9|svn_version:'Unknown'|variable_revision_number:1|show_window:True|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Name the output image:HistogramEqualization
    Bins:256
    Mask:Leave blank
    Local:Yes
    Tile Size:100
    Clip limit:0.01
    Is you image 3D?:No
    Do framewise calculation?:No
    Tile Size (Z):5

HistogramMatching:[module_num:10|svn_version:'Unknown'|variable_revision_number:1|show_window:True|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:DNA
    Name the output image:HistogramMatching
    Is you image 3D?:No
    Use a frame within image as reference?:No
    Image to use as reference :None
    Frame number:5
"""
)

# Mas515/Image_analysis 1_Kuo_seg.cppipe
_KUO_SEGMENTATION_PIPELINE = (
    _SOURCE.format(image="GaussianFilterGFP")
    + """HistogramEqualization:[module_num:8|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:['256 bin size']|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:GaussianFilterGFP
    Name the output image:HistogramEqualizationGFP
    Bins:200
    Mask:Leave blank
    Local:Yes
    Tile Size:50
    Clip limit:0.01
    Is you image 3D?:Yes
    Do framewise calculation?:Yes
    Tile Size (Z):5
"""
)

# Mas515/Image_analysis 2_Kuotracked.cppipe
_KUO_TRACKING_PIPELINE = (
    _SOURCE.format(image="ImageAfterMathAF647Invert")
    + """DistanceTransform:[module_num:31|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:ImageAfterMathAF647Invert
    Name the output image:DistanceTransformAF647
    Rescale values from 0 to 1?:No
"""
)

# TrynkaLab/tglow-pipeline assets/cellprofiler/CELL_DIVIDER/2d_v1.cppipe. The
# block is disabled there; it is enabled here so that it imports. The
# GaussianFilter block only provides the reference image.
_TGLOW_PIPELINE = (
    _SOURCE.format(image="ctv")
    + """GaussianFilter:[module_num:2|enabled:True]
    Select the input image:ctv
    Name the output image:actin
    Sigma:1

HistogramMatching:[module_num:9|svn_version:'Unknown'|variable_revision_number:1|show_window:False|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]
    Select the input image:ctv
    Name the output image:ctv_eq
    Is your image 3D?:No
    Use a frame within image as reference?:No
    Image to use as reference :actin
    Frame number:5
    Plane number in 3d:0
"""
)


@pytest.mark.parametrize(
    ("pipeline", "steps"),
    (
        (
            _PLUGINS_TEST_PIPELINE,
            (
                ("distance_transform", {}),
                ("histogram_equalization", {"local": True, "tile_size": 100}),
                ("histogram_matching", {}),
            ),
        ),
        (
            _KUO_SEGMENTATION_PIPELINE,
            (
                (
                    "histogram_equalization",
                    {
                        "bins": 200,
                        "local": True,
                        "planes_form_a_volume": True,
                        "framewise": True,
                    },
                ),
            ),
        ),
        (_KUO_TRACKING_PIPELINE, (("distance_transform", {"rescale": False}),)),
        (
            _TGLOW_PIPELINE,
            (("gaussian_filter", {}), ("histogram_matching", {})),
        ),
    ),
    ids=("plugins_test_pipeline", "kuo_segmentation", "kuo_tracking", "tglow"),
)
def test_real_pipeline_blocks_import_as_steps_with_the_plugin_settings(
    tmp_path: Path,
    pipeline: str,
    steps: tuple[tuple[str, dict[str, object]], ...],
) -> None:
    """Imported steps keep only the settings that differ from the plugin defaults."""
    cppipe_path = tmp_path / "pipeline.cppipe"
    cppipe_path.write_text(pipeline, encoding="utf-8")

    imported, _pipeline_config = import_cellprofiler_pipeline(cppipe_path)

    settings_of_steps = []
    for step in imported:
        (invocation,) = normalize_function_pattern(step.func).iter_items()
        function = invocation.contract.resolve_canonical_raw_callable()
        settings_of_steps.append(
            (
                invocation.contract.function_name,
                {
                    name: value
                    for name, value in invocation.kwargs_dict.items()
                    if name in inspect.signature(function).parameters
                },
            )
        )
    assert tuple(settings_of_steps) == steps
