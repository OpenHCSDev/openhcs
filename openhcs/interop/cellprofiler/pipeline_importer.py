"""CellProfiler ``.cppipe`` files as an OpenHCS pipeline format."""

from __future__ import annotations

from pathlib import Path

from openhcs.core.pipeline_document import PipelineDocument
from openhcs.core.pipeline_import import PipelineImporter
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline


class CellProfilerPipelineImporter(PipelineImporter):
    suffix = ".cppipe"
    title = "CellProfiler Pipelines"

    @classmethod
    def read(cls, path: Path) -> PipelineDocument:
        steps, config = import_cellprofiler_pipeline(path)
        return PipelineDocument(pipeline_config=config, pipeline_steps=list(steps))
