from __future__ import annotations

from pathlib import Path

import numpy as np
import pytest
import tifffile

from openhcs.agent.dto.config import ConfigPatch
from openhcs.agent.dto.execution import PipelineSourceArtifactPlanInspectionRequest
from openhcs.agent.dto.plate import PlatePathInspectionRequest
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.config_service import ConfigService
from openhcs.agent.services.execution_session_service import ExecutionSessionService
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.core.config import LazyWellFilterConfig, PipelineConfig
from openhcs.core.config_document import ConfigDocumentAuthority
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.dataset_sources.source import (
    DatasetSource,
    FormatSpecificSource,
    RemoteServiceSource,
    SourceSelectionRole,
)
from openhcs.microscopes.imagexpress import ImageXpressHandler
from openhcs.core.dataset_sources.openhcs_format import OpenHCSDatasetSource
from openhcs.microscopes.opera_phenix import OperaPhenixHandler
from openhcs.processing.backends.processors.numpy_processor import percentile_normalize
from openhcs.demo.synthetic_data import (
    SyntheticMicroscopyGenerator,
)
from tests.unit.bioformats_fixture import bioformats_filemanager
from openhcs.core.dataset_sources.choice import (
    AutoDetectedSource,
    DatasetSourceChoice,
)


def _write_valid_opera_phenix_plate(root: Path) -> None:
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(root),
        grid_size=(2, 2),
        tile_size=(8, 8),
        overlap_percent=0,
        stage_error_px=1,
        wavelengths=3,
        z_stack_levels=1,
        num_cells=0,
        wells=["D09"],
        format="OperaPhenix",
        random_seed=1,
    )
    for channel in (1, 2, 3):
        tifffile.imwrite(
            generator.images_dir / f"r04c09f1p01-ch{channel}sk1fk1fl1.tiff",
            np.full((8, 8), channel, dtype=np.uint16),
        )
    generator.generate_opera_phenix_index_xml(root.name)


def test_every_registered_source_declares_its_identity_role_and_backends() -> None:
    sources = DatasetSource.__registry__
    assert sources
    for source_name, source_type in sources.items():
        assert source_type.source_name == source_name
        assert DatasetSourceChoice.named(source_name) is source_type
        assert issubclass(source_type.source_selection_role(), SourceSelectionRole)
        assert source_type.metadata_handler_class is not None
    assert DatasetSourceChoice.choices() == (AutoDetectedSource, *sources.values())
    order = DatasetSource.detection_order()
    assert order[0].source_selection_role().role_name == "prepared_workspace"
    assert set(order) == set(sources.values())


@pytest.mark.parametrize(
    "handler_type",
    (ImageXpressHandler, OperaPhenixHandler, OpenHCSDatasetSource),
)
@pytest.mark.parametrize("missing", (False, True))
def test_metadata_detection_uses_each_declared_owner(
    monkeypatch, tmp_path: Path, handler_type, missing: bool,
) -> None:
    from polystore.exceptions import MetadataNotFoundError

    observed = []
    filemanager = bioformats_filemanager()
    metadata_type = handler_type.metadata_handler_class

    def find_metadata_file(metadata, plate_folder):
        observed.append((type(metadata), plate_folder))
        if missing:
            raise MetadataNotFoundError("declared metadata unavailable")
        return plate_folder / "declared-metadata"

    monkeypatch.setattr(metadata_type, "find_metadata_file", find_metadata_file)

    assert handler_type.detect(tmp_path, filemanager) is not missing
    assert observed == [(metadata_type, tmp_path)]


def test_config_schema_patch_and_source_share_opera_handler_identity() -> None:
    service = ConfigService()
    schema = service.describe_schema("pipeline")
    microscope_field = next(
        field for field in schema.fields if field.path == "dataset_source"
    )

    assert microscope_field.enum_values == tuple(
        choice.source_name for choice in DatasetSourceChoice.choices()
    )
    assert "opera_phenix" in microscope_field.enum_values
    assert "OperaPhenix" not in microscope_field.enum_values

    config_ref = service.create(
        "pipeline",
        ConfigPatch(
            config_type="PipelineConfig",
            values={"dataset_source": "opera_phenix"},
        ),
    )
    config = service.resolve_ref(config_ref)
    rendered = service.render_source(config_ref)

    assert config.dataset_source is OperaPhenixHandler
    assert "dataset_source=OperaPhenixHandler" in rendered.source
    assert (
        ConfigDocumentAuthority.from_source(
            rendered.source,
            expected_config_type=PipelineConfig,
        ).dataset_source
        is OperaPhenixHandler
    )


def test_handler_factory_uses_exact_declared_identity(tmp_path: Path) -> None:
    handler = DatasetSourceChoice.named("opera_phenix").open(tmp_path, filemanager=bioformats_filemanager())

    assert isinstance(handler, OperaPhenixHandler)
    assert handler.source_name == "opera_phenix"
    with pytest.raises(ValueError, match="Unknown dataset source 'OperaPhenix'"):
        DatasetSourceChoice.named("OperaPhenix").open(tmp_path, filemanager=bioformats_filemanager())


def test_source_selection_role_owns_local_availability_contract(
    tmp_path: Path,
) -> None:
    missing_path = tmp_path / "missing"
    file_path = tmp_path / "image.tif"
    file_path.touch()

    with pytest.raises(FileNotFoundError, match=str(missing_path)):
        FormatSpecificSource.require_available_source(
            missing_path
        )
    with pytest.raises(NotADirectoryError, match=str(file_path)):
        FormatSpecificSource.require_available_source(
            file_path
        )

    RemoteServiceSource.require_available_source(missing_path)


def test_explicit_inspection_and_artifact_plan_reach_opera_axes(
    tmp_path: Path,
) -> None:
    _write_valid_opera_phenix_plate(tmp_path)
    path_policy = AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,),
        writable_roots=(tmp_path,),
    )
    inspection = PlateInspectionService(
        path_policy,
        filemanager_factory=type(
            "BioFormatsFileManagerFactory",
            (),
            {"create": staticmethod(bioformats_filemanager)},
        )(),
    ).inspect(
        PlatePathInspectionRequest.from_fields(
            plate_path=str(tmp_path),
            microscope_type="opera_phenix",
        )
    )

    assert inspection.errors == ()
    assert inspection.detected_microscope_type == "opera_phenix"
    assert inspection.available_microscope_types == tuple(
        sorted(DatasetSource.__registry__)
    )
    assert inspection.image_files.count == 3

    config = PipelineConfig(
        dataset_source=OperaPhenixHandler,
        well_filter_config=LazyWellFilterConfig(well_filter="R04C09"),
    )
    pipeline_source = PipelineDocumentAuthority.render(
        PipelineDocumentAuthority.from_values(
            pipeline_config=config,
            pipeline_steps=[FunctionStep(func=percentile_normalize)],
        )
    )
    artifact_plan = ExecutionSessionService(
        path_policy=path_policy,
        pipeline_service=object(),
        config_service=ConfigService(),
    ).inspect_pipeline_source_artifact_plan_request(
        PipelineSourceArtifactPlanInspectionRequest.from_fields(
            plate_path=str(tmp_path),
            pipeline_source=pipeline_source,
            axis_filter=["R04C09"],
        )
    )

    assert artifact_plan.errors == ()
    assert artifact_plan.axes == ("R04C09",)
    assert artifact_plan.source_workspace.axis_file_counts == {"R04C09": 3}
