"""The one-shot G1 cutover converts pre-G1 pycodify sources onto the axis family.

The fixtures were rendered by pre-G1 ``main`` (34abdf41e). This test and its
fixtures are deleted with ``tools/cutover/g1_axis_family.py``.
"""

from __future__ import annotations

import importlib.util
import shutil
from pathlib import Path

import openhcs
from openhcs.core.axes import ColourAxis, StackAxis, Ungrouped
from openhcs.core.config import (
    FijiDimensionMode,
    GlobalPipelineConfig,
    NapariDimensionMode,
)
from openhcs.core.config_document import ConfigDocumentAuthority
from openhcs.core.pipeline.funcstep_contract_validator import (
    FuncStepContractValidator,
)
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.domains.microscopy.axes import Microscopy

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]
FIXTURES = REPO_ROOT / "tests" / "fixtures" / "g1_cutover"


def _cutover():
    spec = importlib.util.spec_from_file_location(
        "g1_axis_family_cutover", REPO_ROOT / "tools" / "cutover" / "g1_axis_family.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _migrated(tmp_path: Path, fixture: str, name: str) -> tuple[Path, str]:
    target = tmp_path / name
    shutil.copy(FIXTURES / fixture, target)
    original = target.read_text()
    assert _cutover().migrate(target) is True
    assert (tmp_path / f"{name}.pre-g1").read_text() == original
    return target, original


def test_pre_g1_pipeline_loads_and_validates_on_the_axis_family(tmp_path) -> None:
    target, original = _migrated(tmp_path, "pre_g1_pipeline.py.fixture", "pipeline.py")
    assert "VariableComponents" in original and "GroupBy.NONE" in original

    document = PipelineDocumentAuthority.from_source(target.read_text())

    normalize, project = document.pipeline_steps
    assert project.processing_config.variable_components == [Microscopy.ZIndex]
    assert project.processing_config.group_by is Ungrouped
    assert project.napari_streaming_config.colour_mode is NapariDimensionMode.LAYER
    assert project.napari_streaming_config.partition_mode is NapariDimensionMode.LAYER
    assert project.fiji_streaming_config.stack_mode is FijiDimensionMode.FRAME
    assert document.pipeline_config.sequential_processing_config.sequential_components == [
        Microscopy.Channel
    ]
    for step in document.pipeline_steps:
        FuncStepContractValidator.validate_funcstep(step)
    assert normalize.name == "normalize"


def test_pre_g1_config_document_loads_on_the_axis_family(tmp_path) -> None:
    target, _ = _migrated(
        tmp_path, "pre_g1_global_config.config.fixture", "global_config.config"
    )

    config = ConfigDocumentAuthority.from_source(
        target.read_text(), expected_config_type=GlobalPipelineConfig
    )

    assert config.sequential_processing_config.sequential_components == [
        Microscopy.Timepoint
    ]


def test_function_requirement_decorators_become_role_declarations() -> None:
    source = (
        "from openhcs.constants.constants import GroupBy, VariableComponents\n"
        "from openhcs.core.pipeline.function_contracts import (\n"
        "    allowed_group_by,\n"
        "    required_variable_components,\n"
        ")\n"
        "\n"
        "@allowed_group_by(GroupBy.CHANNEL)\n"
        "@required_variable_components(VariableComponents.Z_INDEX)\n"
        "def fn(image):\n"
        "    return image\n"
    )

    rewritten = _cutover().rewrite_source(source)

    namespace: dict[str, object] = {}
    exec(compile(rewritten, "<rewritten>", "exec"), namespace)
    assert "@allowed_group_by_roles(ColourAxis)" in rewritten
    assert "@required_axis_roles(StackAxis)" in rewritten
    assert namespace["ColourAxis"] is ColourAxis
    assert namespace["StackAxis"] is StackAxis
    assert "constants" not in rewritten


def test_already_migrated_source_is_left_unchanged(tmp_path) -> None:
    target = tmp_path / "pipeline.py"
    shutil.copy(FIXTURES / "pre_g1_pipeline.py.fixture", target)
    tool = _cutover()
    assert tool.migrate(target) is True
    migrated = target.read_text()
    (tmp_path / "pipeline.py.pre-g1").unlink()
    assert tool.migrate(target) is False
    assert target.read_text() == migrated
    assert not (tmp_path / "pipeline.py.pre-g1").exists()
