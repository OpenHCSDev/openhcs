"""CellProfiler 4 built-in modules that had no OpenHCS declaration.

Each case below is a settings block taken from a published pipeline. The
shared tests ask the same thing of every case: the module resolves, the block
parses and imports, and every setting row is accounted for. The rest of the
file checks what each module means in OpenHCS: SaveCroppedObjects against the
files CellProfiler 4.2.8.1 itself wrote (``tests/fixtures/
cellprofiler_builtin_gap_modules``, produced by ``make_reference.py``), and the
two modules that execute nothing against their settings checks.
"""

from __future__ import annotations

import ast
import inspect
import json
import re
import shutil
import warnings
from dataclasses import dataclass, replace
from pathlib import Path

import imageio.v3 as iio
import numpy as np
import pytest
import tifffile
from polystore.base import ensure_storage_registry, storage_registry
from polystore.filemanager import FileManager

from benchmark.converter.cppipe_corpus import in_tree_cppipe_corpus
from openhcs.agent.services.artifact_plan_inspection_service import (
    AgentProgressQueue,
    CompileInspectionInput,
    InProcessCompileInspectionGateway,
)
from openhcs.core.artifacts.kinds import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.config import (
    SourceBindingsConfig,
    GlobalPipelineConfig,
    LazyNapariStreamingConfig,
    LazyPathPlanningConfig,
)
from openhcs.core.dataset_sources.source_bindings_source import SourceBindingsSource
from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.materialization import FileBundleOptions, MaterializationSpec
from openhcs.core.materialization.core import materialize
from openhcs.core.orchestrator.execution_result import MergeAllRuntimeRecords
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.processing_contracts import Pure2DAuxiliaryOutputAggregator
from openhcs.core.progress import ProgressExecutionContext
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_binding_workspace import SourceBindingWorkspaceProjector
from openhcs.core.source_bindings import (
    FromFileName,
    MetadataExtractionRule,
    PairAsListed,
)
from openhcs.core.source_metadata import SourceMetadataFields
from openhcs.core.steps.function_step import FunctionStep
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    SettingsOnlyCellProfilerModule,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.module_settings import UnmappedModuleSettingsError
from openhcs.interop.cellprofiler.parser import CPPipeParser, ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline
from openhcs.interop.cellprofiler.settings_binder import SettingsBinder
from tests.context_support import executing_context
from tests.materialization_plans import output_plan

_HEADER = (
    "|svn_version:'Unknown'|variable_revision_number:{revision}|show_window:False"
    "|notes:[]|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]"
)

def _preceding_modules(images: tuple[str, ...], *, process_as_3d: bool) -> str:
    """Modules loading ``images`` and making the objects ``Cells`` from the first."""
    assignments = "".join(
        f"""    Select the image type:Grayscale image
    Name to assign these images:{image}
    Select the rule criteria:and (file does contain "{image}")
"""
        for image in images
    )
    return f"""CellProfiler Pipeline: https://cellprofiler.org
NamesAndTypes:[module_num:1|enabled:True]
    Process as 3D?:{"Yes" if process_as_3d else "No"}
    Relative pixel spacing in X:1.0
    Relative pixel spacing in Y:1.0
    Relative pixel spacing in Z:1.0
    Assignments count:{len(images)}
{assignments}ConvertImageToObjects:[module_num:2|variable_revision_number:1|enabled:True]
    Select the input image:{images[0]}
    Name the output objects:Cells
    Convert to boolean image:Yes
    Preserve original labels:No
    Background label:0
    Connectivity:1
"""


@dataclass(frozen=True)
class RealBlock:
    """One module block of a published pipeline and what importing it yields."""

    module_name: str
    source: str
    text: str
    steps: tuple[str, ...]
    """Steps the block itself becomes; () for a module that executes nothing."""


REAL_BLOCKS = (
    RealBlock(
        module_name="LabelImages",
        # CellProfiler/CellProfiler, tests/frontend/resources/modules/labelimages/
        # v1.pipeline, commit b6afe692e1728cae71504d19f3421d4895e83ebf. The file is
        # a 2010 pipeline whose setting labels start with '#'; this is the same
        # block as CellProfiler 4.2.8.1 writes it back after loading that file.
        source="CellProfiler/CellProfiler tests/frontend/resources/modules/labelimages/v1.pipeline",
        text=(
            "LabelImages:[module_num:3"
            + _HEADER.format(revision=1)
            + """
    Number of image sites per well:3
    Number of columns per plate:48
    Number of rows per plate:32
    Order of image data:Column
"""
        ),
        steps=(),
    ),
    RealBlock(
        module_name="SaveCroppedObjects",
        # abestroka/JUMP_vision_model, rad_pipeline/cropped_cells.cppipe, commit
        # 2bb7a079e59531191118856a125505120b0317ca, module 28, settings verbatim.
        source="abestroka/JUMP_vision_model rad_pipeline/cropped_cells.cppipe",
        text=(
            "SaveCroppedObjects:[module_num:3"
            + _HEADER.format(revision=3)
            + """
    Do you want to save cropped images or object masks?:Images
    Objects:Cells
    Directory:Default Output Folder|Argonne/git_repos/JUMP_vision_model/rad_pipeline/segmented_image_temp
    Prefix saved crop image name with input image name?:No
    Select image name to use as a prefix:None
    Save output crops in nested folders?:No
    Saved file format:png
    Image to crop:ImageAfterMath
"""
        ),
        steps=("SaveCroppedObjects",),
    ),
    RealBlock(
        module_name="CreateBatchFiles",
        # BodenmillerGroup/ImcSegmentationPipeline, resources/pipelines/
        # 1_prepare_ilastik.cppipe, commit 3c4639a34d02abfbd01286131fef58202a0f5b7b,
        # module 12, settings verbatim. The published block is disabled; it is
        # enabled here so that the import reads it.
        source="BodenmillerGroup/ImcSegmentationPipeline resources/pipelines/1_prepare_ilastik.cppipe",
        text=(
            "CreateBatchFiles:[module_num:3"
            + _HEADER.format(revision=8)
            + """
    Store batch files in default output folder?:Yes
    Output folder path:/mnt/f2160748-a937-44bd-aca8-3adb8a839612/Data/Analysis/cp4_segmentation_example/cpout
    Are the cluster computers running Windows?:No
    Hidden- in batch mode:No
    Hidden- in distributed mode:No
    Hidden- default input folder at time of save:/home/vitoz
    Hidden- revision number:0
    Hidden- from old matlab:No
    Local root path:/home/vitoz
    Cluster root path:/home/vitoz
"""
        ),
        steps=(),
    ),
)

_BY_NAME = {case.module_name: case for case in REAL_BLOCKS}
_real_blocks = pytest.mark.parametrize(
    "case", REAL_BLOCKS, ids=[case.module_name for case in REAL_BLOCKS]
)


def _pipeline_text(
    block_text: str,
    *,
    images: tuple[str, ...] = ("DNA", "ImageAfterMath"),
    process_as_3d: bool = False,
) -> str:
    return _preceding_modules(images, process_as_3d=process_as_3d) + block_text


def _import(tmp_path: Path, block_text: str) -> list[FunctionStep]:
    cppipe_path = tmp_path / "pipeline.cppipe"
    cppipe_path.write_text(_pipeline_text(block_text), encoding="utf-8")
    steps, _pipeline_config = import_cellprofiler_pipeline(cppipe_path)
    return steps


def _block(tmp_path: Path, block_text: str) -> ModuleBlock:
    cppipe_path = tmp_path / "block.cppipe"
    cppipe_path.write_text(_pipeline_text(block_text), encoding="utf-8")
    return CPPipeParser().parse(cppipe_path)[-1]


def _read_settings(block: ModuleBlock) -> None:
    """Read every setting row the way the import does, failing on an unread one."""
    module_type = CellProfilerModule.declaration_for_block(block)
    module_type.validate_pipeline_import(block)
    if not module_type.emits_function_step():
        return
    coverage = module_type.bind_settings(block, binder=SettingsBinder()).setting_coverage
    assert len(coverage) == len(block.iter_settings())
    assert all(record.status.is_covered for record in coverage)


def _with_setting(text: str, setting: str, value: str | None) -> str:
    """Replace one setting row's value, or drop the row when ``value`` is None."""
    lines = text.splitlines()
    (index,) = (
        position
        for position, line in enumerate(lines)
        if line.strip().startswith(setting + ":")
    )
    lines[index : index + 1] = [] if value is None else [f"    {setting}:{value}"]
    return "\n".join(lines) + "\n"


@_real_blocks
def test_module_resolves(case: RealBlock) -> None:
    module_type = CellProfilerModule.for_module(case.module_name)

    assert module_type is not None
    assert module_type.module_name == case.module_name
    assert module_type.emits_function_step() is bool(case.steps)


@_real_blocks
def test_real_block_parses_and_imports(case: RealBlock, tmp_path: Path) -> None:
    block = _block(tmp_path, case.text)
    assert block.name == case.module_name
    assert len(block.iter_settings()) == len(case.text.strip().splitlines()) - 1

    steps = _import(tmp_path, case.text)

    assert [step.name for step in steps] == ["ConvertImageToObjects", *case.steps]


@_real_blocks
def test_every_setting_row_of_the_real_block_is_read(
    case: RealBlock, tmp_path: Path
) -> None:
    block = _block(tmp_path, case.text)
    _read_settings(block)

    block.setting_records.append(ModuleSetting("Not a setting of this module", "1"))
    with pytest.raises(UnmappedModuleSettingsError, match="not_a_setting_of_this_module"):
        _read_settings(block)


def test_disabled_block_is_not_read(tmp_path: Path) -> None:
    """A disabled module is skipped whatever its settings say."""
    disabled = _BY_NAME["LabelImages"].text.replace("enabled:True", "enabled:False")

    steps = _import(
        tmp_path, _with_setting(disabled, "Order of image data", "Diagonal")
    )

    assert [step.name for step in steps] == ["ConvertImageToObjects"]


@pytest.mark.parametrize(
    ("module_name", "setting", "value", "message"),
    (
        ("LabelImages", "Number of image sites per well", "0", "at least 1, got '0'"),
        ("LabelImages", "Number of columns per plate", "twelve", "at least 1"),
        ("LabelImages", "Number of rows per plate", "2.5", "at least 1"),
        ("LabelImages", "Order of image data", "Diagonal", r"one of \('Row', 'Column'\)"),
        ("LabelImages", "Number of rows per plate", None, "missing the settings"),
        (
            "CreateBatchFiles",
            "Are the cluster computers running Windows?",
            "Maybe",
            "must be Yes/No",
        ),
        ("CreateBatchFiles", "Hidden- revision number", "latest", "cannot accept"),
        ("CreateBatchFiles", "Hidden- in batch mode", "2", "must be Yes/No"),
    ),
)
def test_module_that_executes_nothing_still_refuses_a_bad_setting(
    module_name: str, setting: str, value: str | None, message: str, tmp_path: Path
) -> None:
    case = _BY_NAME[module_name]
    assert issubclass(
        CellProfilerModule.require_module(module_name), SettingsOnlyCellProfilerModule
    )

    with pytest.raises(ValueError, match=message) as error:
        _import(tmp_path, _with_setting(case.text, setting, value))

    assert f"{module_name}(3)" in str(error.value)


def test_label_images_block_in_its_2010_spelling_fails_loudly(tmp_path: Path) -> None:
    """The parser drops rows whose label starts with '#', so nothing is guessed."""
    legacy = (
        "LabelImages:[module_num:3"
        + _HEADER.format(revision=1)
        + """
    # sites / well\\x3A:3
    # of columns\\x3A:48
    # of rows\\x3A:32
    Order\\x3A:Column
"""
    )

    with pytest.raises(UnmappedModuleSettingsError, match="order"):
        _import(tmp_path, legacy)


@pytest.mark.parametrize(
    ("setting", "value", "message"),
    (
        ("Directory", "Elsewhere...|/data/crops", "'Elsewhere...' is not supported"),
        ("Directory", "Default Input Folder|", "'Default Input Folder' is not supported"),
        (
            "Directory",
            "Default Input Folder sub-folder|crops",
            "'Default Input Folder sub-folder' is not supported",
        ),
        (
            "Directory",
            "Default Output Folder sub-folder|../outside",
            "must be a path below the output folder",
        ),
        (
            "Directory",
            "Default Output Folder sub-folder|/absolute",
            "must be a path below the output folder",
        ),
        ("Directory", "Default Output Folder sub-folder|", "must be a path below"),
        (
            "Directory",
            "Default Output Folder sub-folder|(?P<Well>crops)",
            "uses metadata tags",
        ),
        ("Saved file format", "jpeg", "CropFileFormat cannot be coerced from 'jpeg'"),
        (
            "Do you want to save cropped images or object masks?",
            "Outlines",
            "CropExport cannot be coerced from 'Outlines'",
        ),
        ("Image to crop", "None", "saves cropped images but 'Image to crop'"),
        (
            "Prefix saved crop image name with input image name?",
            "Yes",
            "prefixes file names with an image's file name but",
        ),
        ("Save output crops in nested folders?", "Sometimes", "must be Yes/No"),
    ),
)
def test_save_cropped_objects_refuses_what_it_cannot_honour(
    setting: str, value: str, message: str, tmp_path: Path
) -> None:
    text = _with_setting(_BY_NAME["SaveCroppedObjects"].text, setting, value)

    with pytest.raises(ValueError, match=message):
        _import(tmp_path, text)


def test_save_cropped_objects_step_round_trips_through_pipeline_source(
    tmp_path: Path,
) -> None:
    steps = _import(tmp_path, _BY_NAME["SaveCroppedObjects"].text)

    source = FunctionStepTransportAuthority.source_from_pipeline(steps)
    namespace: dict[str, object] = {}
    exec(compile(source, "saved_pipeline.py", "exec"), namespace)
    reconstructed = FunctionStepTransportAuthority.pipeline_steps_from_namespace(
        namespace
    )

    assert FunctionStepTransportAuthority.source_from_pipeline(reconstructed) == source
    (invocation,) = normalize_function_pattern(reconstructed[-1].func).iter_items()
    assert invocation.contract.function_name == "save_cropped_objects"
    assert invocation.kwargs_dict["objects_name"] == "Cells"


# --- SaveCroppedObjects against the files CellProfiler 4.2.8.1 wrote ----------

_FIXTURES = Path(__file__).parents[1] / "fixtures" / "cellprofiler_builtin_gap_modules"
_REFERENCE = np.load(_FIXTURES / "reference.npz")
_REFERENCE_FACTS = json.loads((_FIXTURES / "reference.json").read_text())
_NATIVE_CASES = {
    str(block.module_num): block for block in CPPipeParser().parse(_FIXTURES / "cases.cppipe")
}


def _read_image(path: Path) -> np.ndarray:
    return tifffile.imread(path) if path.suffix == ".tiff" else np.asarray(iio.imread(path))


def _object_files(block: ModuleBlock) -> dict[str, np.ndarray]:
    """Run the module's function on the arrays CellProfiler was given."""
    module_type = CellProfilerModule.require_module(block.name)
    settings = module_type.bind_settings(block, binder=SettingsBinder()).kwargs
    inputs = {
        binding.runtime_parameter_name: _REFERENCE[
            "input_" + module_type.artifact_names_for_binding(block, binding)[0]
        ]
        for binding in module_type.active_artifact_bindings(block)
    }
    labels = inputs.pop("labels")
    function = module_type.require_callable(
        module_type.function_variants[0] if labels.ndim == 3 else None
    )
    kwargs = {
        name: value
        for name, value in settings.items()
        if name in inspect.signature(function).parameters
        and name not in ("image_to_crop", "filename_image")
    }
    if "image_to_crop" in inputs:
        kwargs["image_to_crop"] = inputs["image_to_crop"]
    if "filename_image" in inputs:
        kwargs["filename_image"] = ImagePayloadMetadata(
            source_path="/plates/one/" + _REFERENCE_FACTS["source_file_name"]
        ).payload_with(inputs["filename_image"], None)
    image = labels.astype(np.float32)
    returned_image, files = function(image, labels, **kwargs)
    np.testing.assert_array_equal(np.asarray(returned_image), image)
    return files


@pytest.mark.parametrize("case", sorted(_NATIVE_CASES))
def test_save_cropped_objects_writes_the_files_cellprofiler_wrote(
    case: str, tmp_path: Path
) -> None:
    """Same file names and same pixels, in the function and on disk."""
    expected = _REFERENCE_FACTS["files_written"][case]
    assert expected, "CellProfiler wrote no file for this case"

    files = _object_files(_NATIVE_CASES[case])

    assert sorted(files) == expected
    for path, output in files.items():
        native = _REFERENCE[f"file_{case}/{path}"]
        assert output.content.dtype == native.dtype
        np.testing.assert_array_equal(output.content, native)

    ensure_storage_registry()
    filemanager = FileManager(dict(storage_registry))
    materialize(
        MaterializationSpec(FileBundleOptions()),
        data=files,
        path=str(tmp_path / "SaveCroppedObjects_files.pkl"),
        filemanager=filemanager,
        backends=("disk",),
        context=executing_context(filemanager=filemanager),
        output_plan=output_plan(),
    )
    written = sorted(
        path.relative_to(tmp_path).as_posix()
        for path in tmp_path.rglob("*")
        if path.is_file()
    )
    assert written == expected
    for path in written:
        native = _REFERENCE[f"file_{case}/{path}"]
        stored = _read_image(tmp_path / path)
        assert stored.dtype == native.dtype
        np.testing.assert_array_equal(stored, native)


def test_object_files_of_several_images_unite_and_shared_names_are_refused() -> None:
    """Planes of one invocation each add their files; a shared name is an error."""
    first, second, clash = {"a_1.png": 1}, {"b_1.png": 2}, {"a_1.png": 3}

    assert Pure2DAuxiliaryOutputAggregator.aggregate([first, second], "numpy") == {
        "a_1.png": 1,
        "b_1.png": 2,
    }
    with pytest.raises(ValueError, match=r"share the keys \['a_1.png'\]"):
        Pure2DAuxiliaryOutputAggregator.aggregate([first, clash], "numpy")


# --- SaveCroppedObjects run by the orchestrator on a small plate ---------------

_SAVE_CROPPED_OBJECTS = (
    "SaveCroppedObjects:[module_num:3"
    + _HEADER.format(revision=3)
    + """
    Do you want to save cropped images or object masks?:{export}
    Objects:Cells
    Directory:{directory}
    Prefix saved crop image name with input image name?:{prefix}
    Select image name to use as a prefix:{prefix_image}
    Save output crops in nested folders?:No
    Saved file format:{file_format}
    Image to crop:{image}
"""
)


def _plane(value: int, *, second_object: bool = True) -> np.ndarray:
    pixels = np.zeros((12, 15), dtype=np.uint8)
    pixels[1:4, 1:5] = value
    if second_object:
        pixels[6:11, 8:13] = 200
        pixels[8, 10] = 0
    return pixels


def _run_on_plate(
    tmp_path: Path, block_text: str, sources: dict[str, np.ndarray]
) -> tuple[bool, str, dict[str, np.ndarray]]:
    """Import the block, run well A01, and return the crop files it left."""
    plate = tmp_path / "input"
    plate.mkdir()
    for name, pixels in sources.items():
        tifffile.imwrite(plate / name, pixels, photometric="minisblack")
    volumes = any(pixels.ndim == 3 for pixels in sources.values())
    cppipe_path = tmp_path / "pipeline.cppipe"
    cppipe_path.write_text(
        _pipeline_text(block_text, images=("DNA",), process_as_3d=volumes)
    )
    steps, imported = import_cellprofiler_pipeline(cppipe_path)
    source_bindings = replace(
        imported.source_bindings_config,
        metadata_rules=(
            MetadataExtractionRule(
                source=FromFileName,
                pattern=(
                    r"(?P<well>[A-H]\d{2})_s(?P<site>\d+)_w(?P<channel>\d+)"
                    r"_z(?P<z_index>\d+)_t(?P<timepoint>\d+)_DNA\.tif"
                ),
            ),
        ),
    )
    if not volumes:
        source_bindings = replace(source_bindings, source_stack_components=())
    config = replace(
        imported,
        dataset_source=SourceBindingsSource,
        path_planning_config=LazyPathPlanningConfig(
            global_output_folder=tmp_path / "results"
        ),
        source_bindings_config=source_bindings,
        napari_streaming_config=LazyNapariStreamingConfig(enabled=False),
    )
    bundle = (
        InProcessCompileInspectionGateway()
        .compile(
            CompileInspectionInput(
                plate=plate,
                pipeline_document=PipelineDocumentCodec.from_values(
                    pipeline_config=config, pipeline_steps=steps
                ),
                axis_filter=("A01",),
                global_pipeline_config=GlobalPipelineConfig(
                    num_workers=1, use_threading=True
                ),
                progress_queue=AgentProgressQueue(),
            )
        )
        .execution_bundle
    )
    outcome = (
        PipelineOrchestrator(plate, pipeline_config=config)
        .initialize()
        .execute_compiled_bundle(
            execution_bundle=bundle,
            max_workers=1,
            runtime_observation_mode=MergeAllRuntimeRecords,
            progress_queue=AgentProgressQueue(),
            progress_context=ProgressExecutionContext(
                execution_id="save-cropped-objects", subject_id=str(plate)
            ),
        )["A01"]
    )
    results = tmp_path / "results" / "input_openhcs" / "results"
    crops = {
        path.relative_to(results).as_posix(): _read_image(path)
        for path in sorted(results.rglob("*Cells_?.*"))
    }
    error = "" if outcome.is_success() else str(outcome.error_message)
    return outcome.is_success(), error, crops


def test_two_sites_of_a_well_each_leave_their_own_prefixed_crops(
    tmp_path: Path,
) -> None:
    """16-bit crops carry CellProfiler's 0-1 scale: an 8-bit 101 is 101 * 257."""
    succeeded, error, crops = _run_on_plate(
        tmp_path,
        _SAVE_CROPPED_OBJECTS.format(
            export="Images",
            directory="Default Output Folder sub-folder|crops",
            prefix="Yes",
            prefix_image="DNA",
            file_format="16-bit tiff",
            image="DNA",
        ),
        {f"A01_s{site}_w1_z1_t1_DNA.tif": _plane(100 + site) for site in (1, 2)},
    )

    assert succeeded, error
    hollow_square = np.full((5, 5), 200 * 257, dtype=np.uint16)
    hollow_square[2, 2] = 0
    assert sorted(crops) == [
        f"crops/A01_s00{site}_w1_z001_t001_Cells_{number}.tiff"
        for site in (1, 2)
        for number in (1, 2)
    ]
    for site in (1, 2):
        stem = f"crops/A01_s00{site}_w1_z001_t001_Cells"
        np.testing.assert_array_equal(
            crops[f"{stem}_1.tiff"],
            np.full((3, 4), (100 + site) * 257, dtype=np.uint16),
        )
        np.testing.assert_array_equal(crops[f"{stem}_2.tiff"], hollow_square)


def test_adjacent_blocks_each_leave_their_own_files(tmp_path: Path) -> None:
    images = _SAVE_CROPPED_OBJECTS.format(
        export="Images",
        directory="Default Output Folder sub-folder|crops",
        prefix="Yes",
        prefix_image="DNA",
        file_format="8-bit tiff",
        image="DNA",
    )
    masks = _SAVE_CROPPED_OBJECTS.format(
        export="Masks",
        directory="Default Output Folder sub-folder|masks",
        prefix="No",
        prefix_image="None",
        file_format="png",
        image="None",
    ).replace("module_num:3", "module_num:4")

    succeeded, error, crops = _run_on_plate(
        tmp_path, images + masks, {"A01_s1_w1_z1_t1_DNA.tif": _plane(101)}
    )

    assert succeeded, error
    assert sorted(crops) == [
        "crops/A01_s001_w1_z001_t001_Cells_1.tiff",
        "crops/A01_s001_w1_z001_t001_Cells_2.tiff",
        "masks/Cells_1.png",
        "masks/Cells_2.png",
    ]
    np.testing.assert_array_equal(
        crops["crops/A01_s001_w1_z001_t001_Cells_1.tiff"],
        np.full((3, 4), 101, dtype=np.uint8),
    )
    first_object = np.zeros((12, 15), dtype=np.uint8)
    first_object[1:4, 1:5] = 255
    np.testing.assert_array_equal(crops["masks/Cells_1.png"], first_object)


def test_volume_objects_are_written_as_one_volume_each(tmp_path: Path) -> None:
    volume = np.stack((_plane(110), _plane(120), _plane(130, second_object=False)))

    succeeded, error, crops = _run_on_plate(
        tmp_path,
        _SAVE_CROPPED_OBJECTS.format(
            export="Images",
            directory="Default Output Folder|",
            prefix="No",
            prefix_image="None",
            file_format="8-bit tiff",
            image="DNA",
        ),
        {"A01_s1_w1_z1_t1_DNA.tif": volume},
    )

    assert succeeded, error
    assert sorted(crops) == ["Cells_1.tiff", "Cells_2.tiff"]
    np.testing.assert_array_equal(crops["Cells_1.tiff"], volume[:, 1:4, 1:5])
    np.testing.assert_array_equal(crops["Cells_2.tiff"], volume[:2, 6:11, 8:13])


def test_unprefixed_crops_of_two_sites_are_refused_not_overwritten(
    tmp_path: Path,
) -> None:
    succeeded, error, crops = _run_on_plate(
        tmp_path,
        _SAVE_CROPPED_OBJECTS.format(
            export="Masks",
            directory="Default Output Folder|",
            prefix="No",
            prefix_image="None",
            file_format="png",
            image="None",
        ),
        {f"A01_s{site}_w1_z1_t1_DNA.tif": _plane(100 + site) for site in (1, 2)},
    )

    assert not succeeded
    assert "share the keys ['Cells_1.png', 'Cells_2.png']" in error
    assert crops == {}


# --- every built-in CellProfiler module has a declaration ----------------------

_CELLPROFILER_SITE_PACKAGES = Path(
    "/home/ts/code/projects/openhcs/.venv-cellprofiler39/lib/python3.9/site-packages"
)
_CELLPROFILER_TEST_FIXTURE_MODULES = frozenset(
    {"injectimage", "inject_objects", "measurementfixture", "setting_validation"}
)


def _module_names_declared_in(path: Path) -> tuple[str, ...]:
    """Return the ``module_name`` class attributes of one CellProfiler source file."""
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", SyntaxWarning)
        tree = ast.parse(path.read_text(encoding="utf-8-sig"))
    return tuple(
        statement.value.value
        for class_definition in tree.body
        if isinstance(class_definition, ast.ClassDef)
        for statement in class_definition.body
        if isinstance(statement, ast.Assign)
        and isinstance(statement.value, ast.Constant)
        and any(
            isinstance(target, ast.Name) and target.id == "module_name"
            for target in statement.targets
        )
    )


def test_every_built_in_cellprofiler_module_resolves() -> None:
    if not _CELLPROFILER_SITE_PACKAGES.is_dir():
        pytest.skip("the pinned CellProfiler environment is not installed here")
    module_files = tuple(
        path
        for package in ("cellprofiler/modules", "cellprofiler_core/modules")
        for path in sorted((_CELLPROFILER_SITE_PACKAGES / package).glob("*.py"))
        if not path.name.startswith("_")
        and path.stem not in _CELLPROFILER_TEST_FIXTURE_MODULES
    )
    assert module_files, "no CellProfiler module file was found"

    names_by_file = {path.name: _module_names_declared_in(path) for path in module_files}

    assert {
        name: names for name, names in names_by_file.items() if len(names) != 1
    } == {}, "each module file declares exactly one module_name"
    assert sorted(
        name
        for (name,) in names_by_file.values()
        if CellProfilerModule.for_module(name) is None
    ) == []


# --------------------------------------------------------------------------- #
# LoadData: the CSV that names a pipeline's images
# --------------------------------------------------------------------------- #

_PIPELINE_HEADER = "CellProfiler Pipeline: http://www.cellprofiler.org\nVersion:5\n\n"

_BLOCK_OPTIONS = (
    "|svn_version:'Unknown'|variable_revision_number:6|show_window:False|notes:[]"
    "|batch_state:array([], dtype=uint8)|enabled:True|wants_pause:False]\n"
)

# benchmark/cellprofiler_pipelines/ExampleFly.cppipe (in this repository since
# ece9962b1), module 1.
_LOAD_DATA_EXAMPLE_FLY = (
    "LoadData:[module_num:1" + _BLOCK_OPTIONS
    + "    Input data file location:Default Input Folder|workspace\n"
    "    Name of the file:load_data.csv\n"
    "    Load images based on this data?:Yes\n"
    "    Base image location:Default Input Folder|\n"
    "    Process just a range of rows?:No\n"
    "    Rows to process:1,100000\n"
    "    Group images by metadata?:Yes\n"
    "    Select metadata tags for grouping:Position\n"
    "    Rescale intensities?:Yes\n"
)

_TOXPATH_CSV_FOLDER = (
    "D:\\\\CellRecovery\\\\220601_cell recovery_6 4 2 and 0 days\\\\"
    "220613_154914_20220606_cell recovery 6 4 2 and 0 day_2test_toxpath\\\\"
    "220613_154914_Plate 1\\\\load_data_csv"
)
_CELLPAINTING_CSV_FOLDER = (
    "D:\\\\CellRecovery\\\\220525_cell recovery_ 6 4 2 and 0 days\\\\"
    "220528_102915_20220528_cell recovery 6 4 2 and 0 days_cellpainting_1\\\\"
    "220528_102915_Plate 1\\\\load_data_csv"
)

# github.com/broadinstitute/scripts_notebooks_fossa at commit
# 1a81d37b7d47ce4da70282f0f9975d1908771f07:
# cellprofiler/ToxPath_pipeline/analysis.cppipe (blob 591e5b82), module 1.
_LOAD_DATA_TOXPATH = (
    "LoadData:[module_num:1" + _BLOCK_OPTIONS
    + f"    Input data file location:Default Input Folder|{_TOXPATH_CSV_FOLDER}\n"
    "    Name of the file:load_data_with_illum.csv\n"
    "    Load images based on this data?:Yes\n"
    "    Base image location:Default Input Folder|\n"
    "    Process just a range of rows?:No\n"
    "    Rows to process:1,100000\n"
    "    Group images by metadata?:Yes\n"
    "    Select metadata tags for grouping:Well,Site,Plate\n"
    "    Rescale intensities?:Yes\n"
)

# Same repository and commit: cellprofiler/CellPainting_pipeline/analysis.cppipe
# (blob 621902bc), module 1. Its CSV is on the acquisition machine.
_LOAD_DATA_CELLPAINTING = _LOAD_DATA_TOXPATH.replace(
    f"Default Input Folder|{_TOXPATH_CSV_FOLDER}",
    f"Elsewhere...|{_CELLPAINTING_CSV_FOLDER}",
)

_SMOOTH_DNA = (
    "\nGaussianFilter:[module_num:2" + _BLOCK_OPTIONS
    + "    Select the input image:OrigDNA\n"
    "    Name the output image:SmoothDNA\n"
    "    Sigma:1\n"
)

_PLATE_FOLDERS = ("Plate 1/Images", "Plate 2/Images")

# A Cell Painting style table: rows out of file order, folders as written on the
# acquisition machine, the same file names in two plate folders.
_LISTED_ROWS = (
    ("Plate 1", "r01c02f01", {"Plate": "P1", "Well": "A02", "Site": 1}),
    ("Plate 1", "r01c01f02", {"Plate": "P1", "Well": "A01", "Site": 2}),
    ("Plate 1", "r01c01f01", {"Plate": "P1", "Well": "A01", "Site": 1}),
    ("Plate 2", "r01c01f01", {"Plate": "P2", "Well": "A01", "Site": 1}),
)
_CELLPAINTING_CSV = (
    "Image_FileName_OrigDNA,Image_PathName_OrigDNA,Image_FileName_OrigRNA,"
    "Image_PathName_OrigRNA,Metadata_Plate,Metadata_Well,Metadata_Site\n"
    + "".join(
        f"{stem}-ch1.tiff,D:\\run\\{plate}\\Images,{stem}-ch3.tiff,"
        f"D:\\run\\{plate}\\Images,{metadata['Plate']},{metadata['Well']},"
        f"{metadata['Site']}\n"
        for plate, stem, metadata in _LISTED_ROWS
    )
)
_PLAIN_CSV = "Image_FileName_OrigDNA,Metadata_Well\na.tif,A01\n"


def _load_data_pipeline(folder: Path, block: str, csv_text: str | None = None) -> Path:
    pipeline = folder / "analysis.cppipe"
    pipeline.write_text(_PIPELINE_HEADER + block + _SMOOTH_DNA, encoding="utf-8")
    if csv_text is not None:
        name = next(
            line.partition(":")[2]
            for line in block.splitlines()
            if line.strip().startswith("Name of the file:")
        )
        (folder / name).write_text(csv_text, encoding="utf-8")
    return pipeline


def _load_data_bindings(pipeline: Path) -> SourceBindingsConfig:
    _, config = import_cellprofiler_pipeline(pipeline)
    return config.source_bindings_config.to_base_config()


def _plate_files(plate: Path, *, without: str | None = None) -> tuple[Path, ...]:
    """Both plate folders holding every listed file name, plus one unlisted file."""

    files: list[Path] = []
    for folder in _PLATE_FOLDERS:
        (plate / folder).mkdir(parents=True)
        for stem in ("r01c01f01", "r01c01f02", "r01c02f01", "r09c09f09"):
            for channel in ("ch1", "ch3"):
                path = plate / folder / f"{stem}-{channel}.tiff"
                if without is None or not path.as_posix().endswith(without):
                    path.touch()
                    files.append(path)
    return tuple(files)


def _projections(bindings: SourceBindingsConfig, plate: Path, files: tuple[Path, ...]):
    ensure_storage_registry()
    return (
        SourceBindingWorkspaceProjector(bindings)
        .projection_set(plate, files, filemanager=FileManager(dict(storage_registry)))
        .projections
    )


@pytest.mark.parametrize(
    ("block", "missing_file"),
    (
        (_LOAD_DATA_EXAMPLE_FLY, "'load_data.csv'"),
        (_LOAD_DATA_TOXPATH, "'load_data_with_illum.csv'"),
        (
            _LOAD_DATA_CELLPAINTING,
            repr(
                _CELLPAINTING_CSV_FOLDER.replace("\\\\", "\\")
                + "\\load_data_with_illum.csv"
            ),
        ),
    ),
    ids=("example_fly", "toxpath_default_input_folder", "cellpainting_elsewhere"),
)
def test_load_data_without_its_csv_says_which_file_is_missing(
    tmp_path: Path, block: str, missing_file: str
) -> None:
    with pytest.raises(FileNotFoundError) as refused:
        import_cellprofiler_pipeline(_load_data_pipeline(tmp_path, block))
    assert (
        f"LoadData(1) names its images in the CSV file {missing_file}"
        in str(refused.value)
    )


def test_load_data_names_images_pairs_rows_and_carries_metadata(tmp_path: Path) -> None:
    pipeline = _load_data_pipeline(tmp_path, _LOAD_DATA_TOXPATH, _CELLPAINTING_CSV)
    steps, _ = import_cellprofiler_pipeline(pipeline)
    bindings = _load_data_bindings(pipeline)

    # The later module resolves the name the CSV header defines.
    assert len(steps) == 1
    assert [binding.alias for binding in bindings.binding_declarations] == [
        "OrigDNA",
        "OrigRNA",
    ]
    assert bindings.grouping_metadata_fields == ("Well", "Site", "Plate")
    assert {field.name: field.dtype for field in bindings.metadata_fields} == {
        "Plate": str,
        "Well": str,
        "Site": int,
    }
    assert isinstance(bindings.match_plan, PairAsListed)
    assert [
        tuple(listed.path for listed in source_set.files)
        for source_set in bindings.match_plan.source_sets
    ] == [
        (
            f"D:/run/{plate}/Images/{stem}-ch1.tiff",
            f"D:/run/{plate}/Images/{stem}-ch3.tiff",
        )
        for plate, stem, _ in _LISTED_ROWS
    ]

    plate = tmp_path / "plates"
    observed = [
        (
            projection.source_alias,
            projection.ref.backend_address,
            dict(SourceMetadataFields.declared_items(projection.source_metadata)),
        )
        for projection in _projections(bindings, plate, _plate_files(plate))
    ]
    # Image sets are the CSV's rows in the CSV's order, not the plate's file order;
    # the r09c09f09 files the CSV does not list are in no image set.
    assert observed == [
        (alias, f"{plate_folder}/Images/{stem}-{channel}.tiff", metadata)
        for plate_folder, stem, metadata in _LISTED_ROWS
        for alias, channel in (("OrigDNA", "ch1"), ("OrigRNA", "ch3"))
    ]


@pytest.mark.parametrize(
    ("csv_text", "without", "message"),
    (
        (
            _CELLPAINTING_CSV,
            "Plate 2/Images/r01c01f01-ch3.tiff",
            "but the plate has no such file",
        ),
        (
            # Without its folder, a name two plate folders hold names neither.
            _CELLPAINTING_CSV.replace("D:\\run\\Plate 2\\Images", ""),
            None,
            "matches several plate files",
        ),
    ),
    ids=("listed_file_missing", "listed_file_ambiguous"),
)
def test_load_data_rows_the_plate_cannot_satisfy_are_refused_not_shifted(
    tmp_path: Path, csv_text: str, without: str | None, message: str
) -> None:
    bindings = _load_data_bindings(
        _load_data_pipeline(tmp_path, _LOAD_DATA_TOXPATH, csv_text)
    )
    plate = tmp_path / "plates"
    with pytest.raises(ValueError, match=message):
        _projections(bindings, plate, _plate_files(plate, without=without))


def test_load_data_processes_only_the_requested_rows_and_composes_wells(
    tmp_path: Path,
) -> None:
    block = _LOAD_DATA_EXAMPLE_FLY.replace(
        "Process just a range of rows?:No\n    Rows to process:1,100000",
        "Process just a range of rows?:Yes\n    Rows to process:2,3",
    ).replace("tags for grouping:Position", "tags for grouping:Well")
    bindings = _load_data_bindings(
        _load_data_pipeline(
            tmp_path,
            block,
            "Image_URL_OrigDNA,Image_ObjectsFileName_Nuclei,Metadata_Row,Metadata_Column\n"
            "file:///data/a.tif,a_labels.tif,A,01\n"
            "file:///data/b.tif,b_labels.tif,B,02\n"
            "file:///data/c.tif,c_labels.tif,C,03\n"
            "file:///data/d.tif,d_labels.tif,D,04\n",
        )
    )
    assert isinstance(bindings.match_plan, PairAsListed)
    assert [
        (
            {listed.alias: listed.path for listed in source_set.files},
            {item.field: item.value for item in source_set.metadata},
        )
        for source_set in bindings.match_plan.source_sets
    ] == [
        (
            {"OrigDNA": "data/b.tif", "Nuclei": "b_labels.tif"},
            {"Row": "B", "Column": "02", "Well": "B02"},
        ),
        (
            {"OrigDNA": "data/c.tif", "Nuclei": "c_labels.tif"},
            {"Row": "C", "Column": "03", "Well": "C03"},
        ),
    ]
    assert {
        binding.alias: binding.artifact_kind
        for binding in bindings.binding_declarations
    } == {"OrigDNA": ImageArtifactType, "Nuclei": ObjectLabelsArtifactType}


@pytest.mark.parametrize(
    ("block", "csv_text", "message"),
    (
        (
            _LOAD_DATA_TOXPATH.replace("on this data?:Yes", "on this data?:No"),
            _PLAIN_CSV,
            "'Load images based on this data?': 'No'",
        ),
        (
            _LOAD_DATA_TOXPATH.replace("intensities?:Yes", "intensities?:No"),
            _PLAIN_CSV,
            "'Rescale intensities?': 'No'",
        ),
        (
            _LOAD_DATA_TOXPATH.replace(
                "Base image location:Default Input Folder|", "Base image location:URL|"
            ),
            _PLAIN_CSV,
            "'Base image location' has unknown choice 'URL'",
        ),
        (
            _LOAD_DATA_TOXPATH.replace("revision_number:6", "revision_number:4"),
            _PLAIN_CSV,
            "settings revision 4",
        ),
        (
            _LOAD_DATA_TOXPATH.replace(
                "Process just a range of rows?:No\n    Rows to process:1,100000",
                "Process just a range of rows?:Yes\n    Rows to process:5,2",
            ),
            _PLAIN_CSV,
            "'Rows to process' must satisfy",
        ),
        (
            _LOAD_DATA_TOXPATH.replace(
                f"Default Input Folder|{_TOXPATH_CSV_FOLDER}", "Default Output Folder|"
            ),
            _PLAIN_CSV,
            "'Input data file location' is 'Default Output Folder'",
        ),
        (_LOAD_DATA_TOXPATH, _PLAIN_CSV, "groups image sets by metadata tags"),
        (
            _LOAD_DATA_EXAMPLE_FLY,
            "Image_FileName_OrigDNA,Frame_OrigDNA,Metadata_Position\nmovie.avi,3,1\n",
            "selects planes inside multi-plane files",
        ),
        (
            _LOAD_DATA_EXAMPLE_FLY,
            "Image_FileName_OrigDNA,Titration_NaCl_uM,Metadata_Position\na.tif,750,1\n",
            "['Titration_NaCl_uM'] that are neither image, objects nor Metadata_",
        ),
        (
            _LOAD_DATA_EXAMPLE_FLY,
            "Metadata_Position,Metadata_Well\n1,A01\n",
            "names no image",
        ),
        (
            _LOAD_DATA_EXAMPLE_FLY,
            "Image_FileName_OrigDNA,Metadata_Position\n",
            "lists no image sets",
        ),
    ),
    ids=(
        "measurements_only",
        "no_rescaling",
        "base_location_choice",
        "old_revision",
        "row_range",
        "csv_in_output_folder",
        "grouping_tag_absent",
        "frame_column",
        "measurement_column",
        "no_image_column",
        "no_rows",
    ),
)
def test_load_data_refuses_what_it_cannot_carry_out(
    tmp_path: Path, block: str, csv_text: str, message: str
) -> None:
    with pytest.raises(ValueError, match=re.escape(message)):
        import_cellprofiler_pipeline(_load_data_pipeline(tmp_path, block, csv_text))


def test_load_data_refuses_a_second_module_that_names_images(tmp_path: Path) -> None:
    pipeline = tmp_path / "both.cppipe"
    pipeline.write_text(
        _PIPELINE_HEADER
        + "NamesAndTypes:[module_num:1|enabled:True]\n"
        "    Assignments count:1\n"
        "    Select the image type:Grayscale image\n"
        "    Name to assign these images:DNA\n"
        '    Select the rule criteria:and (file does contain "DNA")\n\n'
        + _LOAD_DATA_EXAMPLE_FLY.replace("module_num:1", "module_num:2"),
        encoding="utf-8",
    )
    (tmp_path / "load_data.csv").write_text(_PLAIN_CSV, encoding="utf-8")
    with pytest.raises(ValueError, match=re.escape("already names ('DNA',)")):
        import_cellprofiler_pipeline(pipeline)


def test_example_fly_imports_once_its_csv_is_beside_it(tmp_path: Path) -> None:
    case = next(case for case in in_tree_cppipe_corpus() if case.name == "ExampleFly")
    pipeline = tmp_path / case.cppipe_path.name
    shutil.copy(case.cppipe_path, pipeline)
    (tmp_path / "load_data.csv").write_text(
        "Image_FileName_OrigBlue,Image_FileName_OrigGreen,Image_FileName_OrigRed,"
        "Metadata_Position\n"
        "01_POS002_D.TIF,01_POS002_F.TIF,01_POS002_R.TIF,2\n",
        encoding="utf-8",
    )
    steps, config = import_cellprofiler_pipeline(pipeline)
    bindings = config.source_bindings_config.to_base_config()
    assert len(steps) == 10
    assert [binding.alias for binding in bindings.binding_declarations] == [
        "OrigBlue",
        "OrigGreen",
        "OrigRed",
    ]
    assert bindings.grouping_metadata_fields == ("Position",)


def test_load_data_image_sets_survive_the_pipeline_document(tmp_path: Path) -> None:
    """The listed image sets are part of the saved pipeline, not of the CSV."""
    pipeline = _load_data_pipeline(tmp_path, _LOAD_DATA_TOXPATH, _CELLPAINTING_CSV)
    steps, config = import_cellprofiler_pipeline(pipeline)
    document = PipelineDocumentCodec.from_values(
        pipeline_config=config, pipeline_steps=steps
    )
    (tmp_path / "load_data_with_illum.csv").unlink()

    read_back = PipelineDocumentCodec.from_source(PipelineDocumentCodec.render(document))

    bindings = config.source_bindings_config.to_base_config()
    assert read_back.pipeline_config.source_bindings_config.to_base_config() == bindings
    assert (
        _load_data_bindings(
            _load_data_pipeline(
                tmp_path, _LOAD_DATA_TOXPATH, _CELLPAINTING_CSV.replace("A02", "B07")
            )
        ).declaration_identity()
        != bindings.declaration_identity()
    )
