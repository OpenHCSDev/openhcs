"""Default automatic/named publication through actual registered ImageMath."""
from dataclasses import replace
from hashlib import sha256
import json
from pathlib import Path

import numpy as np
import pytest
from skimage.color import rgb2gray
import tifffile

from openhcs.agent.services.artifact_plan_inspection_service import (
    AgentProgressQueue, CompileInspectionInput, InProcessCompileInspectionGateway,
)
from openhcs.core.config import (
    GlobalPipelineConfig, LazyNapariStreamingConfig, LazyPathPlanningConfig,
    LazyProcessingConfig,
)
from openhcs.core.orchestrator.execution_result import RuntimeObservationMode
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.source_bindings import MetadataExtractionRule, MetadataSource
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_workspace_projection import VirtualWorkspaceSourceProjection
from openhcs.core.virtual_workspace_metadata import (
    OpenHCSMetadataSubdirectories, VirtualWorkspaceSourceProjectionEntries,
)
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline
from openhcs.domains.microscopy.axes import Microscopy
from openhcs.core.dataset_sources.source_bindings_source import SourceBindingsSource


@pytest.mark.parametrize("rgb", (False, True))
def test_registered_mixed_image_math_publishes_once_in_both_operand_orders(tmp_path, rgb):
    scalar = np.arange(180, dtype=np.uint8).reshape(12, 15)
    color = (
        np.stack((scalar, np.full_like(scalar, 32), np.full_like(scalar, 240)), axis=-1)
        if rgb else 255 - scalar
    )
    source = tmp_path / 'input'
    source.mkdir()
    for name, channel, pixels in (('Gray', 1, scalar), ('Color', 2, color)):
        tifffile.imwrite(source / f'A01_s1_w{channel}_z1_t1_{name}.tif', pixels)
    originals = {image: sha256(image.read_bytes()).hexdigest() for image in source.glob('*.tif')}
    fixture = Path(__file__).resolve().parents[1] / 'fixtures/pipelines/image_math_mixed_publication.cppipe'
    steps, imported = import_cellprofiler_pipeline(fixture)
    config = replace(
        imported, dataset_source=SourceBindingsSource,
        processing_config=LazyProcessingConfig(
            variable_components=[Microscopy.ZIndex], group_by=Microscopy.Channel),
        path_planning_config=LazyPathPlanningConfig(global_output_folder=tmp_path / 'results'),
        source_bindings_config=replace(imported.source_bindings_config,
            metadata_rules=(MetadataExtractionRule(source=MetadataSource.FILE_NAME,
                pattern=r'(?P<well>[A-H]\d{2})_s(?P<site>\d+)_w(?P<channel>\d+)_z(?P<z_index>\d+)_t(?P<timepoint>\d+)_(?:Gray|Color)\.tif'),),
            source_stack_components=(), source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5))),
        napari_streaming_config=LazyNapariStreamingConfig(enabled=False),
    )
    document = PipelineDocumentCodec.from_values(pipeline_config=config, pipeline_steps=steps)
    bundle = InProcessCompileInspectionGateway().compile(CompileInspectionInput(
        plate=source, pipeline_document=document, axis_filter=('A01',),
        global_pipeline_config=GlobalPipelineConfig(num_workers=1, use_threading=True),
        progress_queue=AgentProgressQueue(),
    )).execution_bundle
    outcomes = PipelineOrchestrator(source, pipeline_config=config).initialize().execute_compiled_plate(
        execution_bundle=bundle, max_workers=1,
        runtime_observation_mode=RuntimeObservationMode.MERGE_INTO_PARENT,
        progress_queue=AgentProgressQueue(),
        progress_context={'execution_id': 'engineering620-registered',
                          'plate_id': str(source), 'axis_id': ''},
    )
    assert outcomes['A01'].is_success(), outcomes['A01'].error_message
    gray_expected = scalar.astype(np.float32) / 255
    color_expected = rgb2gray(color.astype(np.float32) / 255) if rgb else color.astype(np.float32) / 255
    expected = {'GrayIndependent': gray_expected, 'ColorIndependent': color_expected,
                'Forward': (gray_expected + color_expected) / 2,
                'Reverse': (gray_expected + color_expected) / 2}
    plate = tmp_path / 'results/input_openhcs'
    saved = tuple((plate / 'images').glob('*.tif'))
    assert len(saved) == 4
    persisted = json.loads((plate / 'openhcs_metadata.json').read_text())
    projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(plate, persisted)
    # The lookup intentionally indexes relative and absolute aliases; count the
    # original persisted declarations, not the derived lookup's keys.
    declared = tuple(entry for directory in OpenHCSMetadataSubdirectories(persisted).values()
                     for entry in VirtualWorkspaceSourceProjectionEntries.from_subdirectory(directory).entries.values())
    assert len(declared) == 4
    for name, pixels in expected.items():
        image, = (image for image in saved if image.name.endswith('_' + name + '.tif'))
        np.testing.assert_array_equal(tifffile.imread(image), pixels)
        relative = str(image.relative_to(plate))
        metadata = projection.source_projections_by_virtual_path[relative].persisted_image_metadata()
        assert metadata.source_voxel_spacing == SourceVoxelSpacing((0.5, 0.5))
        assert metadata.source_component_metadata['well'] == 'A01'
        assert metadata.source_component_metadata['channel'] == ('2' if name in ('ColorIndependent', 'Reverse') else '1')
        assert metadata.source_image_names == (name,)
    for image, digest in originals.items():
        assert sha256(image.read_bytes()).hexdigest() == digest
    print('REGISTERED_DEFAULT_PUBLICATION', rgb, len(saved), 'exact elements', sum(pixels.size for pixels in expected.values()))
