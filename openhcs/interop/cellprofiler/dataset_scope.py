"""One dataset row per CellProfiler pipeline found in a source folder."""

from __future__ import annotations

from pathlib import Path
from urllib.parse import quote, unquote

from openhcs.core.dataset_sources.dataset_scopes import (
    DatasetScope,
    DatasetScopeKind,
    DatasetScopeOffer,
)
from openhcs.core.input_workspace import (
    InputWorkspacePreparationRequest,
    InputWorkspacePreparationResult,
)
from openhcs.interop.cellprofiler.plate_workspace import (
    CellProfilerPlateWorkspacePreparer,
    prepare_cellprofiler_input_workspace,
)


class CellProfilerPipelineScope(DatasetScopeKind):
    """A source folder paired with one of its ``.cppipe`` files."""

    marker = "#openhcs-cppipe="

    @classmethod
    def scope_for(cls, root: Path | str, pipeline_path: Path | str) -> DatasetScope:
        root_path = Path(root)
        pipeline = Path(pipeline_path)
        return DatasetScope(
            scope_id=f"{root_path}{cls.marker}{quote(pipeline.name, safe='')}",
            root=root_path,
            kind=cls,
            pipeline_path=pipeline,
        )

    @classmethod
    def parse(cls, scope_id: str) -> DatasetScope:
        root_text, encoded_name = scope_id.rsplit(cls.marker, maxsplit=1)
        root = Path(root_text)
        return DatasetScope(
            scope_id=scope_id,
            root=root,
            kind=cls,
            pipeline_path=root / unquote(encoded_name),
        )

    @classmethod
    def display_name(cls, scope: DatasetScope) -> str:
        return f"{scope.root.name} / {scope.pipeline_path.stem}"

    @classmethod
    def offers(cls, root: Path) -> tuple[DatasetScopeOffer, ...]:
        preparer = CellProfilerPlateWorkspacePreparer.from_paths(root)
        pipelines = preparer.cppipe_paths()
        if not pipelines:
            return ()
        default = preparer.default_cppipe_path()
        return tuple(
            DatasetScopeOffer(
                cls.scope_for(root, pipeline),
                select_by_default=pipeline == default,
            )
            for pipeline in pipelines
        )

    @classmethod
    def prepare_input_workspace(
        cls,
        scope: DatasetScope,
    ) -> InputWorkspacePreparationResult:
        return prepare_cellprofiler_input_workspace(
            InputWorkspacePreparationRequest(
                selected_path=scope.root,
                selected_pipeline_path=scope.pipeline_path,
            )
        )
