"""Real one-field compilation must not prepare unrelated library catalogs."""

from pathlib import Path

from openhcs.agent.services.execution_session_service import (
    AgentProgressQueue,
    CompileInspectionInput,
    InProcessCompileInspectionGateway,
    artifact_plan_inspection_from_compilation,
)
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.processing.backends.cellprofiler.smoothing import reducenoise
from openhcs.processing.backends.lib_registry.registry_service import RegistryService


def test_real_declared_callable_compiles_without_global_catalog(monkeypatch, tmp_path: Path):
    def forbidden_catalog(*args, **kwargs):
        raise AssertionError("A declared callable must not prepare unrelated catalogs")

    monkeypatch.setattr(RegistryService, "get_all_functions_with_metadata", forbidden_catalog)
    plate = tmp_path / "plate"
    SyntheticMicroscopyGenerator(
        output_dir=str(plate), grid_size=(1, 1), tile_size=(64, 64),
        wavelengths=1, z_stack_levels=1, wells=["A01"], num_cells=3,
        random_seed=123, include_all_components=True,
    ).generate_dataset()
    document = PipelineDocumentAuthority.from_values(
        pipeline_config=PipelineConfig(num_workers=1),
        pipeline_steps=[FunctionStep(func=(reducenoise, {
            "patch_size": 3, "patch_distance": 3, "cutoff_distance": 0.1,
        }), name="DeclaredNlm")],
    )
    compiled = InProcessCompileInspectionGateway().compile(CompileInspectionInput(
        plate=plate, pipeline_document=document, axis_filter=(),
        global_pipeline_config=GlobalPipelineConfig(num_workers=1),
        progress_queue=AgentProgressQueue(),
    ))
    assert tuple(compiled.execution_bundle.runtime_contexts) == ("A01",)
    context = compiled.execution_bundle.runtime_contexts["A01"]
    assert len(context.step_plans) == 1
    assert next(iter(context.step_plans.values())).step_name == "DeclaredNlm"
    inspection = artifact_plan_inspection_from_compilation(
        plate_path=str(plate), axis_filter=(), compilation=compiled,
        progress_event_count=0, warnings=(),
    )
    assert inspection.source_workspace.file_count == 1
