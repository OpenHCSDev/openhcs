from pathlib import Path

from openhcs.core.dataset_sources.dataset_scopes import DatasetScope, PlainDatasetScope
from openhcs.interop.cellprofiler.dataset_scope import CellProfilerPipelineScope
from openhcs.ui.shared.plate_scope_identity import PipelineScopeIdentity


def test_cellprofiler_pipeline_scope_keeps_cppipe_identity_inside_plate_segment(
    tmp_path: Path,
) -> None:
    root = tmp_path / "AdvancedSegmentation"
    pipeline_path = root / "BBBC022 Analysis Final.cppipe"

    scope = CellProfilerPipelineScope.scope_for(root, pipeline_path)
    parsed = DatasetScope.parse(scope.scope_id)

    assert "::" not in scope.scope_id
    assert parsed.kind is CellProfilerPipelineScope
    assert parsed.root == root
    assert parsed.pipeline_path == pipeline_path
    assert parsed.display_name == "AdvancedSegmentation / BBBC022 Analysis Final"
    assert parsed.code_value() == scope.scope_id


def test_plain_dataset_scope_is_its_root(tmp_path: Path) -> None:
    scope = DatasetScope.parse(str(tmp_path / "plate"))

    assert scope.kind is PlainDatasetScope
    assert scope.pipeline_path is None
    assert scope.display_name == "plate"
    assert scope.code_value() == tmp_path / "plate"


def test_pipeline_scope_identity_parses_cppipe_plate_scope(tmp_path: Path) -> None:
    scope = CellProfilerPipelineScope.scope_for(
        tmp_path / "AdvancedSegmentation",
        tmp_path / "AdvancedSegmentation" / "BBBC022 Analysis Final.cppipe",
    )

    pipeline_identity = PipelineScopeIdentity.from_plate_scope(scope.scope_id)
    parsed = PipelineScopeIdentity.from_scope_id(pipeline_identity.scope_id)

    assert PipelineScopeIdentity.matches(pipeline_identity.scope_id)
    assert parsed.plate_scope == scope.scope_id


def test_dataset_scope_owns_nested_object_state_scopes(tmp_path: Path) -> None:
    scope = CellProfilerPipelineScope.scope_for(
        tmp_path / "plate",
        tmp_path / "plate" / "analysis.cppipe",
    )

    assert scope.owns_object_state_scope(scope.scope_id)
    assert scope.owns_object_state_scope(f"{scope.scope_id}::pipeline")
    assert scope.owns_object_state_scope(
        f"{scope.scope_id}::functionstep_0::function_0"
    )
    assert not scope.owns_object_state_scope(f"{scope.scope_id}-other")
    assert not scope.owns_object_state_scope("")
