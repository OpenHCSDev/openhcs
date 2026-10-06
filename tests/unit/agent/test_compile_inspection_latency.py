"""The inspection gateway compiles declared callables without catalog warmup."""

from pathlib import Path

import numpy as np
import tifffile

from openhcs.agent.services.execution_session_service import (
    AgentProgressQueue,
    CompileInspectionInput,
    InProcessCompileInspectionGateway,
)
from openhcs.agent.capabilities import get_capability_registry
from openhcs.constants import Microscope
from openhcs.constants.constants import VariableComponents
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyProcessingConfig,
    PipelineConfig,
)
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.source_bindings import (
    LazySourceBindingsConfig,
    MetadataExtractionRule,
    MetadataSource,
    NamedSourceBinding,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
)


def test_compile_inspection_skips_full_catalog_initialization(monkeypatch, tmp_path: Path):
    import openhcs.processing.func_registry as func_registry

    def forbid_full_catalog():
        raise AssertionError("compile inspection must not initialize the full catalog")

    monkeypatch.setattr(func_registry, "_auto_initialize_registry", forbid_full_catalog)
    for channel in (1, 2):
        tifffile.imwrite(
            tmp_path / f"A02_s001_w{channel}_z001_t001.tif",
            np.ones((8, 8), dtype=np.uint8),
        )

    document = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(
            microscope=Microscope.SOURCE_BINDINGS,
            source_bindings_config=LazySourceBindingsConfig(
                metadata_rules=(
                    MetadataExtractionRule(
                        MetadataSource.FILE_NAME,
                        r"^(?P<Well>A02)_s(?P<Site>001)_w(?P<ChannelNumber>[12])_z(?P<ZIndex>001)_t(?P<Timepoint>001)\.tif$",
                    ),
                ),
                bindings=(NamedSourceBinding(alias="Images"),),
            ),
        ),
        pipeline_steps=[
            FunctionStep(
                func=stack_percentile_normalize,
                name="normalize",
                processing_config=LazyProcessingConfig(
                    variable_components=[VariableComponents.CHANNEL],
                ),
            ),
        ],
    )

    result = InProcessCompileInspectionGateway().compile(
        CompileInspectionInput(
            plate=tmp_path,
            pipeline_document=document,
            axis_filter=(),
            global_pipeline_config=GlobalPipelineConfig(),
            progress_queue=AgentProgressQueue(),
        )
    )

    assert result.execution_bundle.runtime_contexts
    assert result.source_workspace_projection is not None


def test_artifact_plan_declares_workspace_metadata_side_effect():
    capability = next(
        item
        for item in get_capability_registry().capabilities
        if item.name == "openhcs_inspect_pipeline_source_artifact_plan"
    )

    assert not capability.read_only
    assert "may_write_plate_workspace_metadata" in capability.side_effects
