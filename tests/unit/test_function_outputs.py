import json
from pathlib import Path
from dataclasses import replace
from types import SimpleNamespace

import numpy as np
import pytest
import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend
from polystore.streaming.viewer_transport import (
    ViewerDisplayConfigABC,
    ViewerStreamKwarg,
    ViewerStreamSourceIdentity,
)
from polystore.virtual_workspace import SourcePixelRef
from zmqruntime.viewer_protocol import ViewerTransportEndpoint

from openhcs.constants.constants import AllComponents, Backend, VariableComponents
from openhcs.core.aligned_image_payload import AlignedImageSliceContext
from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ImageArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.axis_filter import StepAxisFilterResolution, StepAxisFilterSet
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    MaterializedOutputPlan,
    RuntimeArtifactMaterializationPlan,
)
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.components.parser_metaprogramming import FilenameParseResult
from openhcs.core.config import WellFilterMode
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
from openhcs.core.runtime_image_values import (
    ImageMetadataPayload,
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import (
    SourceImageIdentity,
    SourceImageProvenance,
    SourceImageProvenancePlanes,
)
from openhcs.core.source_metadata import (
    SOURCE_PLANE_COUNT_FIELD,
    SOURCE_PLANE_INDEX_FIELD,
    SOURCE_VOXEL_SPACING_FIELD,
    SOURCE_VOXEL_SPACING_UNIT_FIELD,
    SourceVoxelSpacing,
    SourceVoxelSpacingUnit,
)
from openhcs.core.source_projection import SourceProjectionMetadataSerializer
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.core.steps.function_output_identity import (
    FunctionOutputIdentity,
    FunctionOutputPathRequest,
)
from openhcs.core.steps.function_output_manifest import (
    ProducedOutputSemantics,
    step_output_manifest,
)
from openhcs.core.steps.function_artifact_materialization import (
    MaterializedRuntimeArtifact,
    RuntimeArtifactMaterialization,
)
from openhcs.core.steps.function_outputs import (
    MaterializedImageOutputWriter,
    MemoryOutputWriter,
    OpenHCSMetadataWriter,
    RuntimeArtifactMaterializationAuthority,
    MaterializedImageMetadataTarget,
    RuntimeArtifactMetadataTarget,
    StreamOutputsAuthority,
    StreamOutputBatch,
    finalize_function_step_outputs,
)
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.streaming_config_factory import (
    StreamingViewerRuntimeConfig,
    StreamingViewerSurface,
)
from openhcs.core.virtual_workspace_metadata import (
    FIELDS,
    MetadataWriteError,
    VirtualWorkspaceSourceProjectionEntries,
)
from openhcs.microscopes.imagexpress import ImageXpressFilenameParser
from openhcs.microscopes.microscope_interfaces import MetadataHandler
from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.processing.materialization.core import Output
from openhcs.processing.materialization import (
    ImageFileOptions,
    MaterializationSpec,
    MaterializedFilenameIdentity,
)


@pytest.mark.parametrize("backend", [Backend.ZARR.value, "custom-array-store"])
def test_memory_output_writer_projects_runtime_image_payload_for_array_storage(
    backend,
):
    image = np.zeros((2, 3), dtype=np.uint16)
    payload = ImageMetadataPayload(
        data=image,
        metadata=ImagePayloadMetadata(source_dtype="uint16"),
    )

    prepared = MemoryOutputWriter.payloads(
        [payload],
        ["/virtual/A01_s1_w1.tif"],
        SimpleNamespace(write_backend=backend),
    )

    assert len(prepared) == 1
    assert prepared[0] is image


def test_function_step_metadata_follows_runtime_artifact_persistence(
    monkeypatch,
) -> None:
    events = []
    context = SimpleNamespace()
    plan = SimpleNamespace()
    for authority, method_name, event in (
        (MemoryOutputWriter, "write_if_needed", "memory"),
        (MaterializedImageOutputWriter, "write_if_needed", "materialized"),
        (StreamOutputsAuthority, "stream_outputs", "stream"),
        (
            RuntimeArtifactMaterializationAuthority,
            "materialize",
            "runtime_artifacts",
        ),
        (OpenHCSMetadataWriter, "write", "metadata"),
    ):
        monkeypatch.setattr(
            authority,
            method_name,
            lambda _context, _plan, event=event, **_kwargs: (events.append(event), ())[
                1
            ],
        )

    finalize_function_step_outputs(context, plan)

    assert events == [
        "memory",
        "materialized",
        "stream",
        "runtime_artifacts",
        "metadata",
    ]


def test_memory_output_writer_rejects_payload_path_cardinality_mismatch():
    with pytest.raises(ValueError, match="1 payloads for 0 paths"):
        MemoryOutputWriter.payloads(
            [np.zeros((2, 3), dtype=np.uint16)],
            [],
            SimpleNamespace(write_backend=Backend.MEMORY.value),
        )


def test_memory_output_writer_delegates_disk_payload_preparation(monkeypatch):
    image = np.zeros((2, 3), dtype=np.uint16)
    prepared = object()

    def prepare_disk(payloads, paths):
        assert payloads == [image]
        assert paths == ["/virtual/A01_s1_w1.tif"]
        return [prepared]

    monkeypatch.setattr(
        "openhcs.core.steps.function_io.prepare_disk_image_payloads",
        prepare_disk,
    )

    assert MemoryOutputWriter.payloads(
        [image],
        ["/virtual/A01_s1_w1.tif"],
        SimpleNamespace(write_backend=Backend.DISK.value),
    ) == [prepared]


def complete_component_metadata(metadata):
    completed = {"z_index": "1", "timepoint": "1"}
    completed.update(metadata)
    return completed


def expected_viewer_metadata(metadata):
    projected = complete_component_metadata(metadata)
    return {
        component: (
            int(value)
            if component in {"site", "channel", "z_index", "timepoint"}
            else value
        )
        for component, value in projected.items()
        if component in StreamingConfigStub.COMPONENT_ORDER
    }


class FileManagerStub:
    def __init__(self, memory_payloads):
        self.memory_payloads = memory_payloads
        self.saved_batches = []

    def load_batch(self, paths, backend):
        assert backend == Backend.MEMORY.value
        return [self.memory_payloads[path] for path in paths]

    def save_batch(self, data, paths, backend, **kwargs):
        self.saved_batches.append((data, paths, backend, kwargs))

    def ensure_directory(self, path, backend):
        return None


class StreamingConfigStub(ViewerDisplayConfigABC):
    backend = SimpleNamespace(value="napari_stream")
    COMPONENT_ORDER = ("well", "site", "channel", "z_index", "timepoint")
    host = "127.0.0.1"
    port = 5555
    transport_mode = "tcp"

    def component_modes(self):
        return {component: "stack" for component in self.COMPONENT_ORDER}

    def display_payload_extra(self):
        return {}

    def streaming_viewer_surface(self, context):
        return StreamingViewerSurface(
            runtime_config=StreamingViewerRuntimeConfig(
                transport_endpoint=ViewerTransportEndpoint(
                    host=self.host,
                    port=self.port,
                    transport_mode=self.transport_mode,
                ),
                persistent=False,
                viewer_type=ViewerType.NAPARI,
            ),
            display_config=self,
            source=ViewerStreamSourceIdentity(
                microscope_handler=context.microscope_handler,
                plate_path=context.plate_path,
            ),
        )


class ParserStub:
    def bind_component_values(self, metadata, *, extension=None):
        return FilenameParseResult.from_wire_mapping(
            metadata,
            extension=extension or ".tif",
        )

    def parse_filename(self, name):
        stem = Path(name).stem
        well, site, channel = stem.split("_")
        metadata = complete_component_metadata(
            {
                "well": well,
                "site": site.removeprefix("s"),
                "channel": channel.removeprefix("w"),
                "extension": "".join(Path(name).suffixes),
            }
        )
        return FilenameParseResult(
            ((component, metadata.get(component.value)) for component in AllComponents),
            extension=str(metadata["extension"]),
        )

    def construct_filename(self, components):
        metadata = components.components.wire_mapping()
        return (
            f"{metadata['well']}_s{metadata['site']}_w{metadata['channel']}"
            f"{components.extension}"
        )

    def extract_component_coordinates(self, axis_id):
        assert axis_id == "A01"
        return 1, 1


class MetadataHandlerStub:
    get_metadata_pixel_size = MetadataHandler.get_metadata_pixel_size
    get_metadata_grid_dimensions = MetadataHandler.get_metadata_grid_dimensions

    def __init__(self, values=None):
        self.values = values or {}

    def find_metadata_file(self, root):
        return Path(root) / "openhcs_metadata.json"

    def get_component_values(self, _root, component):
        return self.values.get(component, {})

    def get_grid_dimensions(self, _root):
        return (1, 1)

    def get_metadata_grid_dimensions(self, root):
        return list(self.get_grid_dimensions(root))

    def get_pixel_size(self, _root):
        return 1.0

    def get_metadata_grid_dimensions(self, root):
        return list(self.get_grid_dimensions(root))

    def get_metadata_pixel_size(self, root):
        return self.get_pixel_size(root)


class UnknownLayoutMetadataHandlerStub(MetadataHandlerStub):
    def get_grid_dimensions(self, _root):
        raise AssertionError("Metadata serialization requested a strict grid artifact.")

    def get_metadata_grid_dimensions(self, _root):
        return []


class ContextStub:
    pass


def context_stub(filemanager, parser=None):
    context = ContextStub()
    context.filemanager = filemanager
    context.microscope_handler = SimpleNamespace(
        parser=parser or ParserStub(),
        microscope_type="test",
        metadata_handler=MetadataHandlerStub(
            {"channel": {"1": "OrigDNA", "2": "OrigER", "3": "OrigRNA"}}
        ),
    )
    context.plate_path = Path("/tmp/plate")
    context.input_dir = Path("/tmp/plate/images")
    context.execution_runtime = SimpleNamespace(execution_axis_values=("A01",))
    context.axis_id = "A01"
    context.step_axis_filters = {}
    return context


def test_openhcs_metadata_handler_preserves_unknown_layout_for_serialization(
    tmp_path,
):
    plate_root = tmp_path / "plate"
    images_dir = plate_root / "images"
    images_dir.mkdir(parents=True)
    (plate_root / "openhcs_metadata.json").write_text(
        json.dumps(
            {
                FIELDS.SUBDIRECTORIES: {
                    "images": {
                        FIELDS.GRID_DIMENSIONS: [],
                        FIELDS.IMAGE_FILES: [],
                    }
                }
            }
        ),
        encoding="utf-8",
    )
    handler = OpenHCSMetadataHandler(
        FileManager({Backend.DISK.value: DiskStorageBackend()})
    )

    assert handler.get_metadata_grid_dimensions(images_dir) == []
    with pytest.raises(ValueError, match="list of two integers"):
        handler.get_grid_dimensions(images_dir)


def function_step_plan(
    step_name: str,
    variable_components: tuple[VariableComponents, ...] = (),
    pipeline_position: int = 3,
) -> CompiledStepPlan:
    return CompiledStepPlan(
        step_index=pipeline_position,
        step_name=step_name,
        step_type="FunctionStep",
        axis_id="A01",
        streaming_configs={"napari_stream": StreamingConfigStub()},
        artifact_outputs={},
        output_dir=Path("/tmp/output"),
        pipeline_position=pipeline_position,
        step_scope_id=f"step-scope-{pipeline_position}",
        main_input_dependency=StepInputDependency.no_main_flow(),
        variable_components=variable_components,
        compiled_function_pattern=compile_function_pattern(lambda image: image, {}, {}),
    )


def record_output_path(
    context,
    plan,
    path,
    output_context=None,
    image_metadata=None,
    identity=None,
):
    metadata = context.microscope_handler.parser.parse_filename(Path(path).name)
    assert metadata is not None
    output_identity = identity or FunctionOutputIdentity(
        component_values={
            str(component.value): value
            for component, value in metadata.declared_values()
            if value is not None
        },
        extension=metadata.extension,
        source="test output path",
    )
    step_output_manifest(context).record_outputs(
        plan,
        [
            ProducedOutputSemantics.from_output(
                plan,
                path,
                output_identity,
                output_context=output_context,
                image_metadata=image_metadata,
            )
        ],
    )


def test_function_output_identity_preserves_non_axis_source_metadata() -> None:
    identity = FunctionOutputIdentity(
        component_values={"channel": "2", "site": "1"},
        extension=".tif",
        source="test",
    )

    metadata = identity.component_metadata(
        {
            "Run": "Sequence1",
            "Specimen": "DrosophilaEmbryo",
            "ChannelNumber": "1",
            "OpenHCSOriginalSourceMetadata": {"FrameNumber": "0007"},
        }
    )

    assert metadata == {
        "Run": "Sequence1",
        "Specimen": "DrosophilaEmbryo",
        "channel": "2",
        "site": "1",
        "extension": ".tif",
        "OpenHCSOriginalSourceMetadata": {"FrameNumber": "0007"},
    }


def test_step_output_manifest_prefers_main_dependency_over_auxiliary_artifact_inputs():
    context = context_stub(FileManagerStub({}))
    manifest = step_output_manifest(context)

    main_producer = function_step_plan("ErodeImage")
    main_producer.step_scope_id = "main-producer"
    main_producer.pipeline_position = 24
    seed_producer = function_step_plan("ConvertObjectsToImage")
    seed_producer.step_scope_id = "seed-producer"
    seed_producer.pipeline_position = 14

    record_output_path(
        context,
        main_producer,
        "/tmp/output/A01_s1_w1.tif",
        AlignedImageSliceContext.main_flow(
            "MembFinal",
            artifact_kind=ImageArtifactType.value,
        ),
    )
    record_output_path(
        context,
        seed_producer,
        "/tmp/output/A01_s1_w2.tif",
        AlignedImageSliceContext.main_flow(
            "cellSeeds",
            artifact_kind=ImageArtifactType.value,
        ),
    )

    consumer = function_step_plan("Watershed")
    consumer.main_input_dependency = StepInputDependency.step_output(
        source_step_index=24,
        source_step_scope_id="main-producer",
    )

    assert manifest.producer_paths_for(consumer) == ("A01_s1_w1.tif",)
    assert manifest.filter_to_producer_paths(
        consumer,
        ("A01_s1_w1.tif", "A01_s1_w2.tif"),
        context.microscope_handler.parser,
    ) == ["A01_s1_w1.tif"]


def image_payload_with_source_metadata(pixels, metadata, mask=None):
    completed_metadata = complete_component_metadata(metadata)
    return ImagePayloadMetadata(
        source_component_metadata=completed_metadata,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=(completed_metadata,)
        ),
    ).payload_with(pixels, mask)


def test_stream_outputs_unwraps_runtime_image_payloads_before_viewer_backend():
    path = "/tmp/output/A01_s1_w1.tif"
    pixels = np.ones((2, 3), dtype=np.uint16)
    payload = image_payload_with_source_metadata(
        pixels,
        {
            "well": "A01",
            "site": "1",
            "channel": "1",
            "extension": ".tif",
        },
        mask=np.ones_like(pixels, dtype=bool),
    )
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan("IdentifyPrimaryObjects")
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, kwargs)] = filemanager.saved_batches
    assert streamed_paths == [path]
    assert backend == "napari_stream"
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.port == 5555
    assert stream_request.source.metadata.metadata_by_index == (
        expected_viewer_metadata(
            {
                "well": "A01",
                "site": "1",
                "channel": "1",
            }
        ),
    )
    assert stream_request.message_extra == {
        "component_value_domain": {
            "well": ["A01"],
            "site": [1],
            "channel": [1, 2, 3],
            "z_index": [1],
            "timepoint": [1],
        },
        "component_names_metadata": {
            "channel": {"1": "OrigDNA", "2": "OrigER", "3": "OrigRNA"},
            "well": {"A01": None},
            "site": {"1": None},
            "z_index": {"1": None},
            "timepoint": {"1": None},
        },
    }
    assert stream_request.producer.identities[0].to_payload() == {
        "origin": "pipeline",
        "output_kind": "main",
        "output_key": "main",
        "projection_key": "main",
        "step_name": "IdentifyPrimaryObjects",
        "pipeline_position": 3,
        "step_scope_id": "step-scope-3",
        "invocation_key": None,
        "artifact_kind": None,
    }
    assert streamed_data == [pixels]


def test_source_preserving_output_uses_manifest_path_for_materialization_and_streaming():
    source_path = "/tmp/source/A01_s1_w1.tif"
    materialized_path = "/tmp/materialized/A01_s1_w1.tif"
    pixels = np.ones((2, 3), dtype=np.uint16)
    payload = image_payload_with_source_metadata(
        pixels,
        {
            "well": "A01",
            "site": "1",
            "channel": "1",
            "extension": ".tif",
        },
    )
    filemanager = FileManagerStub({source_path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan("MeasureImageIntensity")
    plan.materialized_output = MaterializedOutputPlan(
        output_dir=Path("/tmp/materialized"),
        backend=Backend.ZARR.value,
        plate_root="/tmp/materialized",
        sub_dir=".",
        analysis_results_dir=None,
    )
    step_output_manifest(context).record_outputs(
        plan,
        [
            ProducedOutputSemantics.from_existing_main_flow_path(
                plan,
                source_path,
                context.microscope_handler.parser,
            )
        ],
    )

    MaterializedImageOutputWriter.write_if_needed(context, plan)
    StreamOutputsAuthority.stream_outputs(context, plan)

    materialized_batch, streamed_batch = filemanager.saved_batches
    assert materialized_batch[0][0] is pixels
    assert materialized_batch[1] == [materialized_path]
    assert materialized_batch[2] == Backend.ZARR.value
    assert streamed_batch[1] == [materialized_path]
    assert streamed_batch[2] == "napari_stream"


def test_stream_outputs_respects_compiled_filter_for_streaming_config():
    path = "/tmp/output/A01_s1_w1.tif"
    pixels = np.ones((2, 3), dtype=np.uint16)
    filemanager = FileManagerStub(
        {
            path: image_payload_with_source_metadata(
                pixels,
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "1",
                    "extension": ".tif",
                },
            )
        }
    )
    context = context_stub(filemanager)
    plan = function_step_plan("GaussianBlur")
    config = next(iter(plan.streaming_configs.values()))
    context.step_axis_filters = {
        plan.step_index: StepAxisFilterSet(
            {
                type(config): StepAxisFilterResolution(
                    resolved_axis_values=frozenset({"B03"}),
                    filter_mode=WellFilterMode.INCLUDE,
                    original_filter="B03",
                )
            }
        )
    }
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    assert filemanager.saved_batches == []

    context.axis_id = "B03"
    StreamOutputsAuthority.stream_outputs(context, plan)

    assert len(filemanager.saved_batches) == 1

    context.axis_id = "b03"
    StreamOutputsAuthority.stream_outputs(context, plan)

    assert len(filemanager.saved_batches) == 2


def test_stream_outputs_scope_viewer_layout_to_collapsed_source_components():
    path = "/tmp/output/A01_s1_w1.tif"
    stack_metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=(
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "1",
                    "z_index": "1",
                    "timepoint": "1",
                },
                {
                    "well": "A01",
                    "site": "2",
                    "channel": "1",
                    "z_index": "1",
                    "timepoint": "1",
                },
            )
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    collapsed_metadata = stack_metadata.collapse_leading_plane_axis()
    payload = collapsed_metadata.payload_with(
        np.ones((2, 3), dtype=np.float64),
        None,
    )
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan("CorrectIlluminationCalculate")
    record_output_path(
        context,
        plan,
        path,
        image_metadata=collapsed_metadata,
        identity=FunctionOutputIdentity(
            component_values={
                "well": "A01",
                "channel": 1,
                "z_index": 1,
                "timepoint": 1,
            },
            filename_component_values={
                "well": "A01",
                "site": 1,
                "channel": 1,
                "z_index": 1,
                "timepoint": 1,
            },
            extension=".tif",
            source="collapsed source identity",
        ),
    )

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(_streamed_data, _streamed_paths, _backend, kwargs)] = filemanager.saved_batches
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.display_config.COMPONENT_ORDER == (
        "well",
        "channel",
        "z_index",
        "timepoint",
    )
    assert stream_request.source.metadata.metadata_by_index == (
        {
            "well": "A01",
            "channel": 1,
            "z_index": 1,
            "timepoint": 1,
        },
    )
    assert "site" not in stream_request.message_extra["component_value_domain"]


def test_stream_outputs_restore_manifest_image_metadata_after_memory_serialization():
    path = "/tmp/output/A01_s1_w1.tif"
    pixels = np.ones((2, 3), dtype=np.uint16)
    source_metadata = complete_component_metadata(
        {
            "well": "A01",
            "site": "1",
            "channel": "1",
            "extension": ".tif",
        }
    )
    image_metadata = ImagePayloadMetadata(
        source_component_metadata=source_metadata,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            component_metadata=(source_metadata,)
        ),
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(0, 0),
            source_shape_yx=(2, 3),
        ),
    )
    filemanager = FileManagerStub({path: pixels})
    context = context_stub(filemanager)
    plan = function_step_plan("IdentifyPrimaryObjects")
    record_output_path(
        context,
        plan,
        path,
        image_metadata=image_metadata,
    )

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(_streamed_data, _streamed_paths, _backend, kwargs)] = filemanager.saved_batches
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.item_fields == {
        "spatial_origin_yx": [0, 0],
        "source_spatial_shape_yx": [2, 3],
        "image_metadata": image_metadata.to_viewer_image_metadata(),
    }
    assert stream_request.source.metadata.metadata_by_index == (
        expected_viewer_metadata(source_metadata),
    )


def test_stream_outputs_keeps_scalar_records_from_variable_component_step():
    path = "/tmp/output/A01_s1_w1.tif"
    pixels = np.ones((2, 3), dtype=np.uint16)
    payload = image_payload_with_source_metadata(
        pixels,
        {
            "well": "A01",
            "site": "1",
            "channel": "1",
            "extension": ".tif",
        },
    )
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan(
        "Normalize",
        variable_components=(VariableComponents.SITE,),
    )
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, _kwargs)] = filemanager.saved_batches
    assert streamed_data == [pixels]
    assert streamed_paths == [path]
    assert backend == "napari_stream"


def test_source_metadata_request_declares_volumetric_z_planes():
    pixels = np.ones((3, 4, 5), dtype=np.uint16)
    metadata = ImagePayloadSourceMetadataContext(
        SourceImageIdentity(
            "/tmp/plate/images/A01_s1_w3_z5.tif",
            {
                "well": "A01",
                "site": "1",
                "channel": "3",
                "z_index": "5",
                SOURCE_PLANE_INDEX_FIELD: "0",
                SOURCE_PLANE_COUNT_FIELD: "3",
            },
        )
    ).metadata(pixels)

    assert metadata.source_image_provenance_planes.paths == (
        "/tmp/plate/images/A01_s1_w3_z5.tif",
        "/tmp/plate/images/A01_s1_w3_z5.tif",
        "/tmp/plate/images/A01_s1_w3_z5.tif",
    )
    assert tuple(
        dict(item)
        for item in metadata.source_image_provenance_planes.component_metadata
    ) == (
        {
            "well": "A01",
            "site": "1",
            "channel": "3",
            "z_index": "5",
            SOURCE_PLANE_INDEX_FIELD: "0",
            SOURCE_PLANE_COUNT_FIELD: "3",
        },
        {
            "well": "A01",
            "site": "1",
            "channel": "3",
            "z_index": "6",
            SOURCE_PLANE_INDEX_FIELD: "1",
            SOURCE_PLANE_COUNT_FIELD: "3",
        },
        {
            "well": "A01",
            "site": "1",
            "channel": "3",
            "z_index": "7",
            SOURCE_PLANE_INDEX_FIELD: "2",
            SOURCE_PLANE_COUNT_FIELD: "3",
        },
    )


def test_source_metadata_request_does_not_infer_volumetric_planes_from_scalar_z():
    pixels = np.ones((3, 4, 5), dtype=np.uint16)
    metadata = ImagePayloadSourceMetadataContext(
        SourceImageIdentity(
            "/tmp/plate/images/A01_s1_w3_z5.tif",
            {
                "well": "A01",
                "site": "1",
                "channel": "3",
                "z_index": "5",
            },
        )
    ).metadata(pixels)

    assert not metadata.source_image_provenance_planes.has_values
    assert metadata.source_component_metadata == {
        "well": "A01",
        "site": "1",
        "channel": "3",
        "z_index": "5",
    }


def test_stream_outputs_projects_volumetric_source_stack_as_z_planes():
    class ZIndexParserStub(ParserStub):
        def parse_filename(self, name):
            stem = Path(name).stem
            well, site, channel, z_index = stem.split("_")
            metadata = complete_component_metadata(
                {
                    "well": well,
                    "site": site.removeprefix("s"),
                    "channel": channel.removeprefix("w"),
                    "z_index": z_index.removeprefix("z"),
                    "extension": "".join(Path(name).suffixes),
                }
            )
            return FilenameParseResult(
                (
                    (component, metadata.get(component.value))
                    for component in AllComponents
                ),
                extension=str(metadata["extension"]),
            )

        def construct_filename(self, components):
            metadata = components.components.wire_mapping()
            return (
                f"{metadata['well']}_s{metadata['site']}_w{metadata['channel']}"
                f"_z{metadata['z_index']}{components.extension}"
            )

    path = "/tmp/output/A01_s1_w1_z1.tif"
    pixels = np.ones((2, 5, 6), dtype=np.uint16)
    metadata = ImagePayloadSourceMetadataContext(
        SourceImageIdentity(
            path,
            complete_component_metadata(
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "1",
                    "z_index": "1",
                    SOURCE_PLANE_INDEX_FIELD: "0",
                    SOURCE_PLANE_COUNT_FIELD: "2",
                }
            ),
        )
    ).metadata(pixels)
    payload = metadata.payload_with(pixels, None)
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager, parser=ZIndexParserStub())
    plan = function_step_plan("Resize")
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, kwargs)] = filemanager.saved_batches
    assert streamed_paths == [
        "/tmp/output/A01_s1_w1_z1.tif",
        "/tmp/output/A01_s1_w1_z2.tif",
    ]
    assert backend == "napari_stream"
    assert [item.shape for item in streamed_data] == [(5, 6), (5, 6)]
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.metadata.metadata_by_index == (
        expected_viewer_metadata(
            {"well": "A01", "site": "1", "channel": "1", "z_index": "1"}
        ),
        expected_viewer_metadata(
            {"well": "A01", "site": "1", "channel": "1", "z_index": "2"}
        ),
    )


def test_stream_outputs_projects_declared_channel_stack_axis():
    path = "/tmp/output/A01_s1_w1.tif"
    pixels = np.ones((2, 5, 6), dtype=np.uint16)
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(path, path),
            component_metadata=(
                complete_component_metadata(
                    {
                        "well": "A01",
                        "site": "1",
                        "channel": "1",
                        "z_index": "1",
                    }
                ),
                complete_component_metadata(
                    {
                        "well": "A01",
                        "site": "1",
                        "channel": "2",
                        "z_index": "1",
                    }
                ),
            ),
        ),
    ).payload_with(pixels, None)
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan(
        "CalculateMath",
        variable_components=(VariableComponents.CHANNEL,),
    )
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, kwargs)] = filemanager.saved_batches
    assert streamed_paths == ["/tmp/output/A01_s1_w1.tif", "/tmp/output/A01_s1_w2.tif"]
    assert backend == "napari_stream"
    assert [item.shape for item in streamed_data] == [(5, 6), (5, 6)]
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.metadata.metadata_by_index == (
        expected_viewer_metadata(
            {"well": "A01", "site": "1", "channel": "1", "z_index": "1"}
        ),
        expected_viewer_metadata(
            {"well": "A01", "site": "1", "channel": "2", "z_index": "1"}
        ),
    )


def test_stream_outputs_projects_stack_planes_with_item_source_paths():
    path = "/tmp/output/A01_s1_w1.tif"
    first_path = "/tmp/source/A01_s1_w1.tif"
    second_path = "/tmp/source/A01_s1_w2.tif"
    pixels = np.ones((2, 5, 6), dtype=np.uint16)
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=(first_path, second_path),
            component_metadata=(
                complete_component_metadata(
                    {
                        "well": "A01",
                        "site": "1",
                        "channel": "1",
                        "z_index": "1",
                    }
                ),
                complete_component_metadata(
                    {
                        "well": "A01",
                        "site": "1",
                        "channel": "2",
                        "z_index": "1",
                    }
                ),
            ),
        ),
    ).payload_with(pixels, None)
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan(
        "MeasureColocalization",
        variable_components=(VariableComponents.CHANNEL,),
    )
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, kwargs)] = filemanager.saved_batches
    assert streamed_paths == ["/tmp/output/A01_s1_w1.tif", "/tmp/output/A01_s1_w2.tif"]
    assert backend == "napari_stream"
    assert [item.shape for item in streamed_data] == [(5, 6), (5, 6)]
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.metadata.metadata_by_index == (
        expected_viewer_metadata(
            {"well": "A01", "site": "1", "channel": "1", "z_index": "1"}
        ),
        expected_viewer_metadata(
            {"well": "A01", "site": "1", "channel": "2", "z_index": "1"}
        ),
    )


def test_stream_outputs_rejects_unaddressed_stack_payload_metadata():
    path = "/tmp/output/A01_s1_w1.tif"
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_component_metadata=complete_component_metadata(
            {
                "well": "A01",
                "site": "1",
                "channel": "1",
            }
        ),
    ).payload_with(np.ones((2, 5, 6), dtype=np.uint16), None)
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan("Resize")
    record_output_path(context, plan, path)

    with pytest.raises(ValueError, match="per-slice component metadata"):
        StreamOutputsAuthority.stream_outputs(context, plan)


def test_stream_outputs_projects_semantic_image_stack_before_viewer_backend():
    path = "/tmp/output/A01_s1_w1.tif"
    pixels = np.ones((2, 3, 4, 3), dtype=np.uint8)
    first_metadata = complete_component_metadata(
        {"well": "A01", "site": "1", "channel": "1"}
    )
    second_metadata = complete_component_metadata(
        {"well": "A01", "site": "1", "channel": "2"}
    )
    payload = ImagePayloadMetadata(
        source_channel_axis=-1,
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=(
            SourceImageProvenancePlanes.from_components(
                component_metadata=(first_metadata, second_metadata)
            )
        ),
    ).payload_with(pixels, None)
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan("OverlayObjects")
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, kwargs)] = filemanager.saved_batches
    assert streamed_paths == ["/tmp/output/A01_s1_w1.tif", "/tmp/output/A01_s1_w2.tif"]
    assert backend == "napari_stream"
    assert [item.shape for item in streamed_data] == [(3, 4, 3), (3, 4, 3)]
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.source.item_fields == {
        "source_channel_axis": -1,
        "image_metadata": ImagePayloadMetadata(
            source_channel_axis=-1
        ).to_viewer_image_metadata(),
    }
    assert stream_request.source.metadata.metadata_by_index == (
        expected_viewer_metadata(first_metadata),
        expected_viewer_metadata(second_metadata),
    )
    assert stream_request.message_extra["component_names_metadata"] == {
        "channel": {"1": "OrigDNA", "2": "OrigER", "3": "OrigRNA"},
        "well": {"A01": None},
        "site": {"1": None},
        "z_index": {"1": None},
        "timepoint": {"1": None},
    }
    assert stream_request.message_extra["component_value_domain"] == {
        "well": ["A01"],
        "site": [1],
        "channel": [1, 2, 3],
        "z_index": [1],
        "timepoint": [1],
    }
    assert stream_request.producer.identities[0].output_key == "main"


def test_stream_outputs_batches_named_main_outputs_by_projection():
    main_path = "/tmp/output/A01_s1_w1.tif"
    artifact_path = "/tmp/output/A01_s1_w2.tif"
    filemanager = FileManagerStub(
        {
            main_path: image_payload_with_source_metadata(
                np.ones((2, 3), dtype=np.uint16),
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "1",
                    "extension": ".tif",
                },
            ),
            artifact_path: image_payload_with_source_metadata(
                np.ones((2, 3), dtype=np.uint16) * 2,
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "2",
                    "extension": ".tif",
                },
            ),
        }
    )
    context = context_stub(filemanager)
    plan = function_step_plan("OverlayOutlines")
    record_output_path(context, plan, main_path)
    record_output_path(
        context,
        plan,
        artifact_path,
        output_context=AlignedImageSliceContext.main_flow(
            "OverlayImage",
            artifact_kind=ImageArtifactType.value,
        ),
    )

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, kwargs)] = filemanager.saved_batches
    assert streamed_paths == [main_path, artifact_path]
    assert backend == "napari_stream"
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert tuple(
        producer.output_key for producer in stream_request.producer.identities
    ) == ("main", "OverlayImage")
    assert [payload.shape for payload in streamed_data] == [(2, 3), (2, 3)]


def test_stream_outputs_partitions_one_producer_by_image_axis_fields():
    scalar_path = "/tmp/output/A01_s1_w1.tif"
    color_path = "/tmp/output/A01_s1_w2.tif"
    scalar_metadata = complete_component_metadata(
        {"well": "A01", "site": "1", "channel": "1"}
    )
    color_metadata = complete_component_metadata(
        {"well": "A01", "site": "1", "channel": "2"}
    )
    filemanager = FileManagerStub(
        {
            scalar_path: ImagePayloadMetadata(
                source_component_metadata=scalar_metadata,
                source_image_provenance_planes=(
                    SourceImageProvenancePlanes.from_components(
                        component_metadata=(scalar_metadata,)
                    )
                ),
            ).payload_with(np.ones((2, 3), dtype=np.uint16), None),
            color_path: ImagePayloadMetadata(
                source_channel_axis=-1,
                source_component_metadata=color_metadata,
                source_image_provenance_planes=(
                    SourceImageProvenancePlanes.from_components(
                        component_metadata=(color_metadata,)
                    )
                ),
            ).payload_with(np.ones((2, 3, 3), dtype=np.uint8), None),
        }
    )
    context = context_stub(filemanager)
    plan = function_step_plan("UntangleWorms")
    record_output_path(context, plan, scalar_path)
    record_output_path(
        context,
        plan,
        color_path,
        output_context=AlignedImageSliceContext.main_flow(
            "WormMask",
            artifact_kind=ImageArtifactType.value,
        ),
    )

    StreamOutputsAuthority.stream_outputs(context, plan)

    assert len(filemanager.saved_batches) == 2
    scalar_batch, color_batch = filemanager.saved_batches
    assert scalar_batch[1] == [scalar_path]
    assert color_batch[1] == [color_path]
    assert scalar_batch[3][
        ViewerStreamKwarg.STREAM_REQUEST.value
    ].source.item_fields == {
        "image_metadata": ImagePayloadMetadata().to_viewer_image_metadata()
    }
    assert color_batch[3][
        ViewerStreamKwarg.STREAM_REQUEST.value
    ].source.item_fields == {
        "source_channel_axis": -1,
        "image_metadata": ImagePayloadMetadata(
            source_channel_axis=-1
        ).to_viewer_image_metadata(),
    }


def test_stream_outputs_rejects_unidentified_stack_without_per_slice_metadata():
    path = "/tmp/output/A01_s1_w1.tif"
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_component_metadata=complete_component_metadata(
            {"well": "A01", "site": "1", "channel": "1"}
        ),
    ).payload_with(np.ones((8, 520, 696), dtype=np.uint16), None)
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan("IdentifyPrimaryObjects")
    record_output_path(context, plan, path)

    with pytest.raises(ValueError, match="per-slice component metadata"):
        StreamOutputsAuthority.stream_outputs(context, plan)


def test_stream_outputs_keeps_recorded_main_stream():
    path = "/tmp/output/A01_s1_w1.tif"
    pixels = np.ones((2, 3), dtype=np.uint16)
    filemanager = FileManagerStub(
        {
            path: image_payload_with_source_metadata(
                pixels,
                {
                    "well": "A01",
                    "site": "1",
                    "channel": "1",
                    "extension": ".tif",
                },
            )
        }
    )
    context = context_stub(filemanager)
    plan = function_step_plan("EnhanceOrSuppressFeatures", pipeline_position=4)
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    [(streamed_data, streamed_paths, backend, kwargs)] = filemanager.saved_batches
    assert streamed_data == [pixels]
    assert streamed_paths == [path]
    assert backend == "napari_stream"
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    assert stream_request.producer.identities[0].output_kind == "main"


def test_stream_outputs_restores_exact_identity_for_reloaded_passthrough() -> None:
    path = "/tmp/output/A01_s1_w2.tif"
    filemanager = FileManagerStub({path: np.ones((2, 3), dtype=np.uint16)})
    context = context_stub(filemanager)
    plan = function_step_plan("MeasureObjectIntensity", pipeline_position=5)
    record_output_path(context, plan, path)

    StreamOutputsAuthority.stream_outputs(context, plan)

    stream_request = filemanager.saved_batches[0][3][
        ViewerStreamKwarg.STREAM_REQUEST.value
    ]
    assert stream_request.source.metadata.metadata_by_index == (
        {
            "well": "A01",
            "site": 1,
            "channel": 2,
            "z_index": 1,
            "timepoint": 1,
        },
    )


def test_stream_outputs_skips_object_label_main_flow_payloads():
    path = "/tmp/output/A01_s1_w1.tif"
    payload = image_payload_with_source_metadata(
        np.zeros((2, 3), dtype=np.uint16),
        {
            "well": "A01",
            "site": "1",
            "channel": "1",
            "extension": ".tif",
        },
    )
    filemanager = FileManagerStub({path: payload})
    context = context_stub(filemanager)
    plan = function_step_plan("ResizeObjects")
    record_output_path(
        context,
        plan,
        path,
        output_context=AlignedImageSliceContext.main_flow(
            output_key="Nuclei",
            artifact_kind=ObjectLabelsArtifactType.value,
        ),
    )

    StreamOutputsAuthority.stream_outputs(context, plan)

    assert filemanager.saved_batches == []


def test_image_persistence_skips_object_label_main_flow_payloads():
    path = "/tmp/output/A01_s1_w1.tif"
    filemanager = FileManagerStub({path: object()})
    context = context_stub(filemanager)
    plan = function_step_plan("RelateObjects")
    record_output_path(
        context,
        plan,
        path,
        output_context=AlignedImageSliceContext.main_flow(
            output_key="Children",
            artifact_kind=ObjectLabelsArtifactType.value,
        ),
    )

    assert step_output_manifest(context).image_records_for(plan) == ()


def test_metadata_target_family_discovers_new_declaration_without_consumer_edits(
    tmp_path,
):
    registry = OpenHCSMetadataWriter.OutputTarget.__registry__
    original_keys = set(registry)
    try:

        class SupplementalImageMetadataTarget(OpenHCSMetadataWriter.OutputTarget):
            @classmethod
            def from_plan(cls, plan):
                return cls(
                    output_dir=tmp_path,
                    backend=Backend.DISK.value,
                    plate_root=str(tmp_path),
                    sub_dir="supplemental",
                    results_dir=None,
                )

        plan = function_step_plan("memory-only")
        plan.write_backend = Backend.MEMORY.value
        context = context_stub(FileManagerStub({}))
        (target,) = OpenHCSMetadataWriter.OutputTarget.for_plan(plan)
        assert type(target) is SupplementalImageMetadataTarget
        assert OpenHCSMetadataWriter.OutputTarget.for_execution(context, plan) == (
            target,
        )
        assert target.produced_projection_entries(context, plan) is None
    finally:
        for key in set(registry) - original_keys:
            del registry[key]


def test_metadata_writer_skips_owner_without_image_outputs():
    path = "/tmp/output/A01_s1_w1.tif"
    filemanager = FileManagerStub({path: object()})
    context = context_stub(filemanager)
    plan = function_step_plan("RelateObjects")
    plan.create_openhcs_metadata = True
    plan.write_backend = Backend.DISK.value
    record_output_path(
        context,
        plan,
        path,
        output_context=AlignedImageSliceContext.main_flow(
            output_key="Children",
            artifact_kind=ObjectLabelsArtifactType.value,
        ),
    )

    OpenHCSMetadataWriter.write(context, plan)


def test_metadata_writer_preserves_unknown_layout_without_resolving_grid_artifact(
    tmp_path,
):
    plate_root = tmp_path / "output_plate"
    output_dir = plate_root / "images"
    output_dir.mkdir(parents=True)
    output_path = output_dir / "A01_s1_w1.tif"
    pixels = np.zeros((4, 5), dtype=np.uint16)
    tifffile.imwrite(output_path, pixels)
    filemanager = FileManager(
        {
            Backend.DISK.value: DiskStorageBackend(),
            Backend.MEMORY.value: MemoryStorageBackend(),
        }
    )
    context = context_stub(filemanager)
    context.filemanager.ensure_directory(output_dir, Backend.MEMORY.value)
    context.filemanager.save(
        ImageMetadataPayload(pixels, ImagePayloadMetadata(source_dtype="uint16")),
        str(output_path),
        Backend.MEMORY.value,
    )
    context.microscope_handler.metadata_handler = UnknownLayoutMetadataHandlerStub(
        {"channel": {"1": "DNA"}}
    )
    context.metadata_cache = {
        AllComponents.WELL: {"A01": None},
        AllComponents.SITE: {"1": None},
        AllComponents.CHANNEL: {"1": "DNA"},
        AllComponents.Z_INDEX: {"1": None},
        AllComponents.TIMEPOINT: {"1": None},
    }
    plan = function_step_plan("Segment nuclei")
    plan.output_dir = output_dir
    plan.output_plate_root = str(plate_root)
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(plate_root / "images_results")
    plan.write_backend = Backend.DISK.value
    plan.create_openhcs_metadata = True
    record_output_path(context, plan, output_path)

    OpenHCSMetadataWriter.write(context, plan)

    subdirectory = json.loads(
        (plate_root / "openhcs_metadata.json").read_text(encoding="utf-8")
    )[FIELDS.SUBDIRECTORIES]["images"]
    assert subdirectory[FIELDS.GRID_DIMENSIONS] == []


@pytest.mark.parametrize("metadata_writer", (False, True))
def test_produced_projection_metadata_persists_typed_collapsed_semantics(
    tmp_path, metadata_writer
):
    plate_root = tmp_path / "output_plate"
    output_dir = plate_root / "images"
    path = output_dir / "A01_s1_w1.tif"
    output_dir.mkdir(parents=True)
    pixels = np.zeros((2, 4, 5), dtype=np.uint16)
    tifffile.imwrite(path, pixels)
    context = context_stub(
        FileManager(
            {
                Backend.DISK.value: DiskStorageBackend(),
                Backend.MEMORY.value: MemoryStorageBackend(),
            }
        )
    )
    context.metadata_cache = {
        AllComponents.WELL: {"A01": None},
        AllComponents.SITE: {"1": None},
        AllComponents.CHANNEL: {"1": None},
        AllComponents.Z_INDEX: {"1": None},
        AllComponents.TIMEPOINT: {"1": None},
    }
    plan = function_step_plan("Mosaic")
    plan.output_dir = output_dir
    plan.output_plate_root = str(plate_root)
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(plate_root / "images_results")
    plan.write_backend = Backend.DISK.value
    plan.create_openhcs_metadata = metadata_writer
    context.step_plans = {plan.step_index: plan}
    metadata = ImagePayloadMetadata(
        source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5)),
        source_component_metadata={
            "well": "A01",
            "channel": "1",
            "z_index": "1",
            "timepoint": "1",
            SOURCE_VOXEL_SPACING_FIELD: "0.5,0.5",
            SOURCE_VOXEL_SPACING_UNIT_FIELD: "micrometers",
        },
        source_provenance=SourceImageProvenance(
            source_component_metadata={
                "well": "A01",
                "channel": "1",
                "z_index": "1",
                "timepoint": "1",
            },
            source_image_provenance_planes=SourceImageProvenancePlanes.from_contributor_components(
                paths=("/source/site-1.tif", "/source/site-2.tif"),
                component_metadata=({"site": "1"}, {"site": "2"}),
            ),
        ),
    )
    record_output_path(
        context,
        plan,
        path,
        image_metadata=metadata,
        identity=FunctionOutputIdentity(
            component_values={
                "well": "A01",
                "channel": "1",
                "z_index": "1",
                "timepoint": "1",
            },
            filename_component_values={
                "well": "A01",
                "site": "1",
                "channel": "1",
                "z_index": "1",
                "timepoint": "1",
            },
            extension=".tif",
            source="collapsed mosaic",
        ),
    )
    context.filemanager.ensure_directory(output_dir, Backend.MEMORY.value)
    context.filemanager.save(
        ImageMetadataPayload(pixels, metadata),
        str(path),
        Backend.MEMORY.value,
    )
    OpenHCSMetadataWriter.write(context, plan)
    OpenHCSMetadataWriter.finalize_completed_plate({"A01": context})

    subdirectory = json.loads(
        (plate_root / "openhcs_metadata.json").read_text(encoding="utf-8")
    )[FIELDS.SUBDIRECTORIES]["images"]
    assert subdirectory[FIELDS.GRID_DIMENSIONS] == []
    assert subdirectory[FIELDS.PIXEL_SIZE] == 0.5
    record = subdirectory[FIELDS.SOURCE_PROJECTION][0]
    restored = ImagePayloadMetadata.from_mapping(
        record[SourceProjectionMetadataSerializer.IMAGE_METADATA_FIELD]
    )
    assert "site" not in restored.source_component_metadata
    assert len(restored.source_provenance.represented_source_identities) == 2
    assert record["address"]["site"] == "1"
    assert "site" not in record["source_metadata"]
    assert subdirectory[FIELDS.SOURCE_METADATA]["images/A01_s1_w1.tif"]["site"] == "1"


def test_runtime_image_artifact_projects_persisted_source_binding(
    tmp_path, monkeypatch
) -> None:
    plate_root = tmp_path / "output_plate"
    output_dir = plate_root / "analysis_inputs"
    output_dir.mkdir(parents=True)
    output_path = (
        output_dir / "A49_s001_w2_z001_t001_neurite_candidate_mask.checkpoint.tif"
    )
    pixels = np.ones((4, 5), dtype=np.uint8)
    tifffile.imwrite(output_path, pixels)
    context = context_stub(
        FileManager(
            {
                Backend.DISK.value: DiskStorageBackend(),
                Backend.MEMORY.value: MemoryStorageBackend(),
            }
        ),
        parser=SourceSchemaFilenameParser(),
    )
    plan = function_step_plan("Neurite checkpoint")
    plan.materialized_output = MaterializedOutputPlan(
        output_dir=output_dir,
        backend=Backend.DISK.value,
        plate_root=str(plate_root),
        sub_dir="analysis_inputs",
        analysis_results_dir=str(plate_root / "analysis_inputs_results"),
    )
    plan.runtime_artifact_materialization = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True,
        persistent_backend=Backend.DISK.value,
    )
    metadata = ImagePayloadMetadata(
        source_component_metadata={
            "well": "A49",
            "site": "1",
            "channel": "2",
            "z_index": "1",
            "timepoint": "1",
        }
    )
    output = Output.from_metadata(
        path=str(output_path),
        content=pixels,
        metadata=metadata,
    )
    materialization = SimpleNamespace(
        spec=SimpleNamespace(participates_in_persistent_materialization=lambda: True),
        output_plan=SimpleNamespace(
            name="neurite_candidate_mask",
            artifact_type=ImageArtifactType,
        ),
        record=SimpleNamespace(
            key=SimpleNamespace(
                scope=RuntimeExecutionAxisScope.from_raw(
                    "A49",
                    component=AllComponents.SITE,
                    value="1",
                    fixed_component_values=(
                        (AllComponents.Z_INDEX, "1"),
                        (AllComponents.TIMEPOINT, "1"),
                    ),
                )
            )
        ),
        outputs=lambda _plan, _context, **_kwargs: (output,),
    )
    saved_artifacts = (
        MaterializedRuntimeArtifact(
            outputs_by_backend={Backend.DISK.value: (output,)},
            materialization=materialization,
        ),
    )

    target = MaterializedImageMetadataTarget.from_plan(plan)
    assert target is not None
    target = replace(target, artifact_materializations=saved_artifacts)
    [(projection, virtual_path)] = target.runtime_artifact_projection_paths(
        context, plan
    )

    artifact_target = RuntimeArtifactMetadataTarget.from_plan(plan)
    assert artifact_target is not None
    assert artifact_target.runtime_artifact_projection_paths(context, plan) == ()

    assert virtual_path == (
        "analysis_inputs/A49_s001_w2_z001_t001_neurite_candidate_mask.checkpoint.tif"
    )
    assert projection.source_alias == "neurite_candidate_mask"
    assert projection.artifact_kind is ImageArtifactType
    assert projection.image_metadata is not None
    assert projection.image_metadata.source_dtype == "uint8"
    assert projection.ref == SourcePixelRef(Backend.DISK.value, virtual_path)
    structured = target.produced_projection_entries(context, plan)
    structured = SourceProjectionMetadataSerializer.projection_fields(
        structured.projection_paths
    )
    assert structured is not None
    [record] = structured[FIELDS.SOURCE_PROJECTION]
    assert record["virtual_path"] == virtual_path
    assert record["source_alias"] == "neurite_candidate_mask"
    assert record["artifact_kind"] == ImageArtifactType.value
    assert (
        record[SourceProjectionMetadataSerializer.IMAGE_METADATA_FIELD]["source_dtype"]
        == "uint8"
    )


def test_runtime_multiplane_label_artifact_projects_persisted_source_binding(
    tmp_path, monkeypatch
) -> None:
    plate_root = tmp_path / "output_plate"
    output_dir = plate_root / "analysis_inputs"
    output_dir.mkdir(parents=True)
    output_path = (
        plate_root
        / "analysis_inputs_results"
        / "A49_z_index-1_timepoint-1_neurite_outgrowth_step0.labels.tif"
    )
    output_path.parent.mkdir(parents=True)
    pixels = np.ones((2, 4, 5), dtype=np.int32)
    tifffile.imwrite(output_path, pixels)
    context = context_stub(
        FileManager(
            {
                Backend.DISK.value: DiskStorageBackend(),
                Backend.MEMORY.value: MemoryStorageBackend(),
            }
        ),
        parser=SourceSchemaFilenameParser(),
    )
    plan = function_step_plan("Neurite labels")
    plan.materialized_output = MaterializedOutputPlan(
        output_dir=output_dir,
        backend=Backend.DISK.value,
        plate_root=str(plate_root),
        sub_dir="analysis_inputs",
        analysis_results_dir=str(plate_root / "analysis_inputs_results"),
    )
    plan.runtime_artifact_materialization = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True,
        persistent_backend=Backend.DISK.value,
    )
    common_metadata = {
        "well": "A49",
        "site": "1",
        "z_index": "1",
        "timepoint": "1",
    }
    metadata = ImagePayloadMetadata(
        source_provenance=SourceImageProvenance(
            source_component_metadata=common_metadata,
            source_image_provenance_planes=(
                SourceImageProvenancePlanes.from_components(
                    paths=("/source/A49_w1.tif", "/source/A49_w2.tif"),
                    component_metadata=(
                        {**common_metadata, "channel": "1"},
                        {**common_metadata, "channel": "2"},
                    ),
                )
            ),
        ),
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    output = Output.from_metadata(
        path=str(output_path),
        content=pixels,
        metadata=metadata,
    )
    materialization = SimpleNamespace(
        spec=SimpleNamespace(participates_in_persistent_materialization=lambda: True),
        output_plan=SimpleNamespace(
            name="neurite_outgrowth",
            artifact_type=ObjectLabelsArtifactType,
        ),
        record=SimpleNamespace(
            key=SimpleNamespace(
                scope=RuntimeExecutionAxisScope.from_raw(
                    "A49",
                    component=AllComponents.SITE,
                    value="1",
                    fixed_component_values=(
                        (AllComponents.Z_INDEX, "1"),
                        (AllComponents.TIMEPOINT, "1"),
                    ),
                )
            )
        ),
        outputs=lambda _plan, _context, **_kwargs: (output,),
    )
    saved_artifacts = (
        MaterializedRuntimeArtifact(
            outputs_by_backend={Backend.DISK.value: (output,)},
            materialization=materialization,
        ),
    )

    output_plan = ArtifactOutputPlan(
        name="neurite_outgrowth",
        path="/memory/neurite_outgrowth.pkl",
        artifact_type=ObjectLabelsArtifactType,
        materialization=MaterializationSpec(ImageFileOptions()),
    )
    plan.artifact_outputs = {output_plan.ref(): output_plan}
    target = RuntimeArtifactMetadataTarget.from_plan(plan)
    assert target is not None
    target = replace(target, artifact_materializations=saved_artifacts)
    [(projection, virtual_path)] = target.runtime_artifact_projection_paths(
        context, plan
    )

    assert virtual_path == (
        "analysis_inputs_results/"
        "A49_z_index-1_timepoint-1_neurite_outgrowth_step0.labels.tif"
    )
    assert projection.artifact_kind is ObjectLabelsArtifactType
    assert projection.address is None
    assert projection.execution_scope == materialization.record.key.scope
    assert projection.image_metadata is not None
    assert projection.image_metadata.source_provenance.source_plane_count == 2
    assert tuple(
        projection.image_metadata.for_source_plane(index).source_component_metadata[
            "channel"
        ]
        for index in range(2)
    ) == ("1", "2")
    structured = target.produced_projection_entries(context, plan)
    structured = SourceProjectionMetadataSerializer.projection_fields(
        structured.projection_paths
    )
    assert structured is not None
    [record] = structured[FIELDS.SOURCE_PROJECTION]
    assert record["artifact_kind"] == ObjectLabelsArtifactType.value
    assert record["address"] is None
    assert record["execution_scope"]["axis_id"] == "A49"
    assert (
        len(
            record[SourceProjectionMetadataSerializer.IMAGE_METADATA_FIELD][
                "source_provenance"
            ]["source_image_provenance_planes"]
        )
        == 2
    )
    restored = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
        structured
    ).entries[virtual_path]
    assert restored.address is None
    assert restored.execution_scope == materialization.record.key.scope
    assert restored.artifact_kind is ObjectLabelsArtifactType
    assert restored.image_metadata is not None
    assert restored.image_metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
    assert restored.image_metadata.source_provenance.source_plane_count == 2


class _QualifierIgnoringParserStub:
    """Parse well/site/channel from filenames with an ignored output qualifier.

    Mirrors the real source-schema parser behavior that produced same-address
    outputs such as ``..._IllumActin.tif`` and ``..._IllumActinAvg.tif``.
    """

    def parse_filename(self, name):
        parts = Path(name).stem.split("_")
        well, site, channel = parts[0], parts[1], parts[2]
        metadata = complete_component_metadata(
            {
                "well": well,
                "site": site.removeprefix("s"),
                "channel": channel.removeprefix("w"),
                "extension": "".join(Path(name).suffixes),
            }
        )
        return FilenameParseResult(
            ((component, metadata.get(component.value)) for component in AllComponents),
            extension=str(metadata["extension"]),
        )

    def bind_component_values(self, metadata, *, extension=None):
        return FilenameParseResult.from_wire_mapping(
            metadata,
            extension=extension or ".tif",
        )


def test_produced_projection_derives_artifact_alias_for_same_address_outputs(
    tmp_path,
):
    plate_root = tmp_path / "output_plate"
    output_dir = plate_root / "images"
    output_dir.mkdir(parents=True)
    first = output_dir / "A01_s1_w1_IllumActin.tif"
    second = output_dir / "A01_s1_w1_IllumActinAvg.tif"
    pixels = np.zeros((4, 5), dtype=np.uint16)
    tifffile.imwrite(first, pixels)
    tifffile.imwrite(second, pixels)
    context = context_stub(
        FileManager(
            {
                Backend.DISK.value: DiskStorageBackend(),
                Backend.MEMORY.value: MemoryStorageBackend(),
            }
        ),
        parser=_QualifierIgnoringParserStub(),
    )
    context.filemanager.ensure_directory(output_dir, Backend.MEMORY.value)
    context.filemanager.save(pixels, str(first), Backend.MEMORY.value)
    context.filemanager.save(pixels, str(second), Backend.MEMORY.value)
    context.metadata_cache = {
        AllComponents.WELL: {"A01": None},
        AllComponents.SITE: {"1": None},
        AllComponents.CHANNEL: {"1": None},
        AllComponents.Z_INDEX: {"1": None},
        AllComponents.TIMEPOINT: {"1": None},
    }
    plan = function_step_plan("SaveImages")
    plan.output_dir = output_dir
    plan.output_plate_root = str(plate_root)
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(plate_root / "images_results")
    plan.write_backend = Backend.DISK.value
    context.step_plans = {plan.step_index: plan}

    record_output_path(
        context,
        plan,
        str(first),
        output_context=AlignedImageSliceContext.main_flow(
            output_key="IllumActin",
            artifact_kind=ImageArtifactType.value,
        ),
    )
    record_output_path(
        context,
        plan,
        str(second),
        output_context=AlignedImageSliceContext.main_flow(
            output_key="IllumActinAvg",
            artifact_kind=ImageArtifactType.value,
        ),
    )

    OpenHCSMetadataWriter.write(context, plan)

    subdirectory = json.loads(
        (plate_root / "openhcs_metadata.json").read_text(encoding="utf-8")
    )[FIELDS.SUBDIRECTORIES]["images"]
    projections = subdirectory[FIELDS.SOURCE_PROJECTION]
    roles = {record["projection_role"] for record in projections}
    assert roles == {"primary_plane", "source_artifact"}
    artifacts = [
        record
        for record in projections
        if record["projection_role"] == "source_artifact"
    ]
    assert [record["source_alias"] for record in artifacts] == ["IllumActinAvg"]
    assert artifacts[0]["address"]["well"] == "A01"
    mapping = subdirectory[FIELDS.WORKSPACE_MAPPING]
    assert set(mapping) == {
        "images/A01_s1_w1_IllumActin.tif",
        "images/A01_s1_w1_IllumActinAvg.tif",
    }


@pytest.mark.parametrize("well", ("A01", "sample.v2", "image.ome.tif"))
@pytest.mark.parametrize("extension", (".tif", ".ome.tif"))
@pytest.mark.parametrize("z_values", ((1, 2, 3), (3, 1), (2,)))
def test_produced_address_publication_never_parses_generated_filenames(
    tmp_path, monkeypatch, well, extension, z_values
):
    """Bounded identity/image publication and durable reconciliation journey."""
    plate_root = tmp_path / "plate"
    output_dir = plate_root / "images"
    output_dir.mkdir(parents=True)
    parser = SourceSchemaFilenameParser()
    filemanager = FileManager(
        {
            Backend.DISK.value: DiskStorageBackend(),
            Backend.MEMORY.value: MemoryStorageBackend(),
        }
    )
    context = context_stub(filemanager, parser=parser)
    context.metadata_cache = {
        AllComponents.WELL: {well: None, "not-produced": None},
        AllComponents.SITE: {"1": None},
        AllComponents.CHANNEL: {"1": "DNA", "99": "not-produced"},
        AllComponents.Z_INDEX: {"1": None, "2": None, "3": None, "99": None},
        AllComponents.TIMEPOINT: {"1": None},
    }
    plan = function_step_plan("typed identity")
    plan.output_dir = output_dir
    plan.output_plate_root = str(plate_root)
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(plate_root / "images_results")
    plan.write_backend = Backend.DISK.value
    plan.create_openhcs_metadata = True
    context.step_plans = {plan.step_index: plan}
    filemanager.ensure_directory(output_dir, Backend.MEMORY.value)
    records = []
    paths = []
    pixels = np.zeros((4, 5), dtype=np.uint16)
    for z_index in z_values:
        source_path = f"{well}_s001_w1_z{z_index:03d}_t001{extension}"
        metadata = ImagePayloadMetadata(
            source_path=source_path,
            source_component_metadata={
                "well": well,
                "site": 1,
                "channel": 1,
                "z_index": z_index,
                "timepoint": 1,
            },
            source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5)),
        )
        identity = FunctionOutputIdentity.from_metadata(
            parser, metadata
        )
        assert identity is not None
        assert identity.extension == extension
        identity = identity.with_filename_qualifier("centre_dots")
        filename = identity.filename(parser)
        assert filename == f"{well}_s001_w1_z{z_index:03d}_t001_centre_dots{extension}"
        # Readback is an external boundary; publication below must not parse.
        parsed = parser.parse_filename(filename)
        assert parsed is not None
        assert parsed.extension == extension
        assert parsed.value_for(AllComponents.WELL) == well
        path = output_dir / filename
        tifffile.imwrite(path, pixels)
        filemanager.save(
            metadata.payload_with(pixels, None), str(path), Backend.MEMORY.value
        )
        records.append(
            ProducedOutputSemantics.from_output(
                plan,
                path,
                identity,
                output_context=AlignedImageSliceContext.main_flow(
                    output_key="centre_dots", artifact_kind=ImageArtifactType.value
                ),
                image_metadata=metadata,
            )
        )
        paths.append(f"images/{filename}")
    step_output_manifest(context).record_outputs(plan, records)

    def reject_generated_path_parse(_filename):
        raise AssertionError("Publication must consume the typed produced address.")

    monkeypatch.setattr(parser, "parse_filename", reject_generated_path_parse)
    OpenHCSMetadataWriter.write(context, plan)
    # Step memory is unavailable at final reconciliation. Durable projections
    # must supply the same addresses, calibration and exact saved coverage.
    for record in records:
        filemanager.delete(record.output_path, Backend.MEMORY.value)
    OpenHCSMetadataWriter.finalize_completed_plate({well: context})
    subdirectory = json.loads((plate_root / "openhcs_metadata.json").read_text())[
        FIELDS.SUBDIRECTORIES
    ]["images"]
    assert set(subdirectory[FIELDS.IMAGE_FILES]) == set(paths)
    assert subdirectory["wells"] == {well: None}
    assert subdirectory["channels"] == {"1": "DNA"}
    assert set(subdirectory["z_indexes"]) == {str(z) for z in z_values}
    assert subdirectory[FIELDS.PIXEL_SIZE] == 0.5
    for record in subdirectory[FIELDS.SOURCE_PROJECTION]:
        assert record["address"]["well"] == well
        assert int(record["address"]["z_index"]) in z_values
        restored = ImagePayloadMetadata.from_mapping(record["image_metadata"])
        assert restored.source_dtype == "uint16"
        assert restored.source_voxel_spacing.values_zyx == (0.5, 0.5)

    metadata_path = plate_root / "openhcs_metadata.json"
    previous_metadata = metadata_path.read_bytes()
    unregistered = output_dir / "unowned_s001_w1_z001_t001.tif"
    tifffile.imwrite(unregistered, pixels)
    with pytest.raises(MetadataWriteError, match="lack typed produced addresses"):
        OpenHCSMetadataWriter.finalize_completed_plate({well: context})
    assert metadata_path.read_bytes() == previous_metadata
    unregistered.unlink()  # This fixture owns the synthetic file.

    if len(paths) > 1:
        removed = paths[0]
        (plate_root / removed).unlink()
        OpenHCSMetadataWriter.finalize_completed_plate({well: context})
        reconciled = json.loads(metadata_path.read_text())[FIELDS.SUBDIRECTORIES][
            "images"
        ]
        assert set(reconciled[FIELDS.IMAGE_FILES]) == set(paths[1:])
        assert removed not in reconciled[FIELDS.WORKSPACE_MAPPING]
        assert removed not in reconciled[FIELDS.SOURCE_METADATA]
        assert {
            record["virtual_path"] for record in reconciled[FIELDS.SOURCE_PROJECTION]
        } == set(paths[1:])
        assert set(reconciled["z_indexes"]) == {str(z) for z in z_values[1:]}


@pytest.mark.parametrize("well", ("A01", "image.ome.tif"))
@pytest.mark.parametrize("extension", (".tif", ".ome.tif"))
def test_produced_stacked_dotted_identity_keeps_declared_extension(
    tmp_path, well, extension
):
    parser = SourceSchemaFilenameParser()
    source_paths = tuple(
        f"/source/{well}_s001_w1_z{z:03d}_t001{extension}" for z in (3, 1, 2)
    )
    metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=source_paths,
        ),
    )
    request = FunctionOutputPathRequest(
        parser=parser,
        output_dir=tmp_path,
        output_payload=metadata.payload_with(
            np.zeros((3, 4, 5), dtype=np.uint16), None
        ),
        input_path=Path(source_paths[0]).name,
        variable_components=(VariableComponents.Z_INDEX,),
    )
    identity = FunctionOutputIdentity.from_request(request)
    assert identity.extension == extension
    assert "z_index" not in identity.component_values
    assert identity.filename_address.value_for(AllComponents.Z_INDEX) == "3"
    assert identity.filename_address.value_for(AllComponents.WELL) == well
    filename = identity.with_filename_qualifier("centre_dots").filename(parser)
    assert filename == f"{well}_s001_w1_z003_t001_centre_dots{extension}"


def test_completed_plate_metadata_includes_outputs_written_after_owner_axis(
    tmp_path,
):
    plate_root = tmp_path / "output_plate"
    images_dir = plate_root / "images"
    images_dir.mkdir(parents=True)
    first_image = images_dir / "A01_s1_w1.tif"
    later_image = images_dir / "B03_s1_w1.tif"
    from polystore.memory import MemoryStorageBackend

    from openhcs.core.image_file_serialization import ImageFileFormat

    first_pixels = np.zeros((4, 5), dtype=np.uint16)
    ImageFileFormat.require_path(first_image).write(first_image, first_pixels)
    # A concurrent axis can persist pixels before publishing its producer
    # record. The first publication must not infer or discard that ownership.
    ImageFileFormat.require_path(later_image).write(later_image, first_pixels)

    filemanager = FileManager(
        {
            Backend.DISK.value: DiskStorageBackend(),
            Backend.MEMORY.value: MemoryStorageBackend(),
        }
    )
    filemanager.ensure_directory(images_dir, Backend.MEMORY.value)
    filemanager.save(first_pixels, str(first_image), Backend.MEMORY.value)
    owner_context = context_stub(filemanager)
    owner_context.metadata_cache = {
        AllComponents.WELL: {"A01": None, "B03": None},
        AllComponents.SITE: {"1": None},
        AllComponents.CHANNEL: {"1": "DNA"},
        AllComponents.Z_INDEX: {"1": None},
        AllComponents.TIMEPOINT: {"1": None},
    }
    owner_plan = function_step_plan("final")
    owner_plan.output_dir = images_dir
    owner_plan.output_plate_root = str(plate_root)
    owner_plan.sub_dir = "images"
    owner_plan.analysis_results_dir = str(plate_root / "images_results")
    owner_plan.write_backend = Backend.DISK.value
    owner_plan.create_openhcs_metadata = True
    owner_context.step_plans = {owner_plan.step_index: owner_plan}
    record_output_path(owner_context, owner_plan, str(first_image))

    OpenHCSMetadataWriter.write(owner_context, owner_plan)
    initial_metadata = json.loads(
        (plate_root / "openhcs_metadata.json").read_text(encoding="utf-8")
    )["subdirectories"]["images"]
    assert initial_metadata["wells"] == {"A01": None}

    follower_context = context_stub(filemanager)
    follower_context.metadata_cache = owner_context.metadata_cache
    follower_plan = function_step_plan("final")
    follower_plan.axis_id = "B03"
    follower_plan.output_dir = images_dir
    follower_plan.output_plate_root = str(plate_root)
    follower_plan.sub_dir = "images"
    follower_plan.analysis_results_dir = str(plate_root / "images_results")
    follower_plan.write_backend = Backend.DISK.value
    follower_context.step_plans = {follower_plan.step_index: follower_plan}
    follower_plan.create_openhcs_metadata = True
    filemanager.save(first_pixels, str(later_image), Backend.MEMORY.value)
    record_output_path(follower_context, follower_plan, str(later_image))
    OpenHCSMetadataWriter.write(follower_context, follower_plan)

    OpenHCSMetadataWriter.finalize_completed_plate(
        {"A01": owner_context, "B03": follower_context}
    )

    metadata = json.loads(
        (plate_root / "openhcs_metadata.json").read_text(encoding="utf-8")
    )["subdirectories"]["images"]
    assert metadata["image_files"] == [
        "images/A01_s1_w1.tif",
        "images/B03_s1_w1.tif",
    ]
    assert metadata["wells"] == {"A01": None, "B03": None}


def test_completed_plate_metadata_skips_unmaterialized_output_target(tmp_path):
    plate_root = tmp_path / "output_plate"
    missing_images_dir = plate_root / "images"
    filemanager = FileManager({Backend.DISK.value: DiskStorageBackend()})
    context = context_stub(filemanager)
    plan = function_step_plan("measurements-only")
    plan.output_dir = missing_images_dir
    plan.output_plate_root = str(plate_root)
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(plate_root / "images_results")
    plan.write_backend = Backend.DISK.value
    plan.create_openhcs_metadata = True
    context.step_plans = {plan.step_index: plan}

    OpenHCSMetadataWriter.finalize_completed_plate({"A01": context})

    assert not (plate_root / "openhcs_metadata.json").exists()


@pytest.mark.parametrize("contents", ["absent", "tables", "images"])
def test_runtime_image_metadata_target_requires_persisted_images(tmp_path, contents):
    directory = tmp_path / "results"
    if contents != "absent":
        directory.mkdir()
        if contents == "tables":
            (directory / "measurements.csv").write_text("ObjectNumber,Area\n1,4\n")
        else:
            tifffile.imwrite(
                directory / "A01_s001_w2_z001_t001.tif", np.ones((2, 2), dtype=np.uint8)
            )
    context = context_stub(FileManager({Backend.DISK.value: DiskStorageBackend()}))
    plan = function_step_plan("SaveImages")
    plan.write_backend = Backend.MEMORY.value
    plan.output_plate_root = str(tmp_path)
    plan.output_dir = directory
    plan.analysis_results_dir = str(directory)
    plan.runtime_artifact_materialization = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True,
        persistent_backend=Backend.DISK.value,
    )
    output_plan = ArtifactOutputPlan(
        name="SavedImage",
        path="/memory/SavedImage.pkl",
        artifact_type=ImageArtifactType,
        materialization=MaterializationSpec(
            ImageFileOptions(
                filename_suffix=".tif",
                filename_identity=MaterializedFilenameIdentity.SOURCE_IDENTITY,
            )
        ),
    )
    plan.artifact_outputs = {output_plan.ref(): output_plan}
    context.runtime_value_store = RuntimeValueStore()
    context.runtime_value_store.record(
        RuntimeValue.normalize(
            output_plan,
            ImageMetadataPayload(
                np.ones((2, 2), dtype=np.uint8),
                ImagePayloadMetadata(
                    source_component_metadata={
                        "well": "A01",
                        "site": "1",
                        "channel": "2",
                        "z_index": "1",
                        "timepoint": "1",
                    }
                ),
            ),
            axis_id="A01",
        ),
        path=output_plan.path,
        backend=Backend.MEMORY.value,
    )
    target = RuntimeArtifactMetadataTarget.from_plan(plan)
    assert target is not None
    assert target.output_dir == directory
    saved_artifacts = ()
    if contents == "images":
        record = context.runtime_value_store.values()[0]
        materialization = RuntimeArtifactMaterialization.from_record(
            output_plan=output_plan,
            record=record,
            plan=plan,
            context=context,
        )
        saved_artifacts = (
            MaterializedRuntimeArtifact(
                outputs_by_backend={
                    Backend.DISK.value: (
                        Output.from_metadata(
                            path=str(directory / "A01_s001_w2_z001_t001.tif"),
                            content=record.value.data,
                            metadata=image_payload_metadata(record.value.data),
                        ),
                    )
                },
                materialization=materialization,
            ),
        )
    selected = OpenHCSMetadataWriter.OutputTarget.for_execution(
        context, plan, artifact_materializations=saved_artifacts
    )
    if contents == "images":
        assert selected == (target,)
    else:
        assert selected == ()
        plan.create_openhcs_metadata = True
        OpenHCSMetadataWriter.write(context, plan)
        assert not (tmp_path / "openhcs_metadata.json").exists()
    assert directory.exists() == (contents != "absent")


@pytest.mark.parametrize("stray_image", [False, True])
def test_declared_image_destinations_publish_and_reconcile_after_value_cleanup(
    tmp_path, stray_image
):
    filemanager = FileManager(
        {
            Backend.DISK.value: DiskStorageBackend(),
            Backend.MEMORY.value: MemoryStorageBackend(),
        }
    )
    context = context_stub(filemanager, parser=SourceSchemaFilenameParser())
    context.runtime_value_store = RuntimeValueStore()
    context.metadata_cache = {}
    context.tiff_config = None
    plan = function_step_plan("Declared image exports")
    plan.streaming_configs = {}
    plan.write_backend = Backend.MEMORY.value
    plan.output_plate_root = str(tmp_path)
    plan.output_dir = tmp_path / "images"
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(tmp_path / "results")
    plan.create_openhcs_metadata = True
    plan.runtime_artifact_materialization = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True,
        persistent_backend=Backend.DISK.value,
    )
    context.step_plans = {plan.step_index: plan}
    components = {
        "well": "A01",
        "site": "1",
        "channel": "2",
        "z_index": "1",
        "timepoint": "1",
    }
    pixels = np.arange(20, dtype=np.uint16).reshape(4, 5)
    payload = ImageMetadataPayload(
        pixels,
        ImagePayloadMetadata(
            source_component_metadata=components,
            source_dtype="uint16",
        ),
    )
    for name, directory in (("Copy", "nested/copies"), ("Review", "review")):
        output_plan = ArtifactOutputPlan(
            name=name,
            path=f"/memory/{name}.pkl",
            artifact_type=ImageArtifactType,
            materialization=MaterializationSpec(
                ImageFileOptions(
                    filename_suffix=".tif",
                    filename_identity=MaterializedFilenameIdentity.SOURCE_IDENTITY,
                    relative_path_template=f"{directory}/A01_s001_w2_z001_t001.tif",
                )
            ),
        )
        plan.artifact_outputs[output_plan.ref()] = output_plan
        context.runtime_value_store.record(
            RuntimeValue.normalize(output_plan, payload, axis_id="A01"),
            path=output_plan.path,
            backend=Backend.MEMORY.value,
        )
    materializations = RuntimeArtifactMaterializationAuthority.materialize(
        context, plan
    )
    OpenHCSMetadataWriter.write(
        context, plan, artifact_materializations=materializations
    )
    context.runtime_value_store.clear()
    if stray_image:
        tifffile.imwrite(tmp_path / "images/review/unowned.tif", pixels)
        with pytest.raises(MetadataWriteError, match="lack typed produced addresses"):
            OpenHCSMetadataWriter.finalize_completed_plate({"A01": context})
        return
    OpenHCSMetadataWriter.finalize_completed_plate({"A01": context})
    subdirectories = json.loads((tmp_path / "openhcs_metadata.json").read_text())[
        FIELDS.SUBDIRECTORIES
    ]
    assert set(subdirectories) == {"images/nested/copies", "images/review"}
    for directory, subdirectory in subdirectories.items():
        path = f"{directory}/A01_s001_w2_z001_t001.tif"
        assert subdirectory[FIELDS.IMAGE_FILES] == [path]
        entries = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
            subdirectory
        ).entries
        assert set(entries) == {path}
        projection = entries[path]
        assert projection.component_value(AllComponents.CHANNEL) == "2"
        assert projection.source_metadata["site"] == "1"
        np.testing.assert_array_equal(tifffile.imread(tmp_path / path), pixels)


@pytest.mark.parametrize("with_raster", [False, True])
def test_actual_array_exports_only_publish_declared_raster_inventory(
    tmp_path, with_raster
):
    """A saved NumPy array is an actual output, without being a raster inventory."""
    filemanager = FileManager(
        {
            Backend.DISK.value: DiskStorageBackend(),
            Backend.MEMORY.value: MemoryStorageBackend(),
        }
    )
    context = context_stub(filemanager, parser=SourceSchemaFilenameParser())
    context.runtime_value_store = RuntimeValueStore()
    context.metadata_cache = {}
    context.tiff_config = None
    plan = function_step_plan("Independent array and raster exports")
    plan.streaming_configs = {}
    plan.write_backend = Backend.MEMORY.value
    plan.output_plate_root = str(tmp_path)
    plan.output_dir = tmp_path / "images"
    plan.sub_dir = "images"
    plan.analysis_results_dir = str(tmp_path / "results")
    plan.create_openhcs_metadata = True
    plan.runtime_artifact_materialization = RuntimeArtifactMaterializationPlan(
        persistent_enabled=True,
        persistent_backend=Backend.DISK.value,
    )
    context.step_plans = {plan.step_index: plan}
    pixels = np.arange(20, dtype=np.float32).reshape(4, 5) / 7
    payload = ImageMetadataPayload(
        pixels,
        ImagePayloadMetadata(
            source_component_metadata={
                "well": "A01",
                "site": "1",
                "channel": "2",
                "z_index": "1",
                "timepoint": "1",
            },
            source_dtype="float32",
            source_voxel_spacing=SourceVoxelSpacing(
                (0.65, 0.65), SourceVoxelSpacingUnit.MICROMETERS
            ),
        ),
    )
    declarations = [("NumericField", "exports/Illum.npy")]
    if with_raster:
        declarations.append(("RasterField", "exports/A01_s001_w2_z001_t001.tif"))
    for name, relative_path in declarations:
        output_plan = ArtifactOutputPlan(
            name=name,
            path=f"/memory/{name}.pkl",
            artifact_type=ImageArtifactType,
            materialization=MaterializationSpec(
                ImageFileOptions(
                    filename_suffix=Path(relative_path).suffix,
                    relative_path_template=relative_path,
                )
            ),
        )
        plan.artifact_outputs[output_plan.ref()] = output_plan
        context.runtime_value_store.record(
            RuntimeValue.normalize(output_plan, payload, axis_id="A01"),
            path=output_plan.path,
            backend=Backend.MEMORY.value,
        )

    materializations = RuntimeArtifactMaterializationAuthority.materialize(
        context, plan
    )
    saved_outputs = tuple(
        output
        for artifact in materializations
        for output in artifact.outputs_for_backend(Backend.DISK.value)
    )
    expected_paths = {
        tmp_path / "images" / relative_path for _name, relative_path in declarations
    }
    assert {Path(output.path) for output in saved_outputs} == expected_paths
    assert all(path.is_file() for path in expected_paths)
    np.testing.assert_array_equal(
        np.load(tmp_path / "images/exports/Illum.npy", allow_pickle=False), pixels
    )
    observed_locations = tuple(
        location
        for artifact in materializations
        for locations in (
            artifact.observation(plan).materialized_locations_by_address.values()
        )
        for location in locations
    )
    assert {Path(location.path) for location in observed_locations} == expected_paths

    OpenHCSMetadataWriter.write(
        context, plan, artifact_materializations=materializations
    )
    context.runtime_value_store.clear()
    OpenHCSMetadataWriter.finalize_completed_plate({"A01": context})
    metadata_path = tmp_path / "openhcs_metadata.json"
    subdirectories = json.loads(metadata_path.read_text())[FIELDS.SUBDIRECTORIES]
    assert set(subdirectories) == {"images/exports"}
    subdirectory = subdirectories["images/exports"]
    assert subdirectory[SourceProjectionMetadataSerializer.RESULTS_DIR_FIELD] == (
        "images/exports"
    )
    if not with_raster:
        assert subdirectory[FIELDS.IMAGE_FILES] == []
        assert (
            VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
                subdirectory
            ).entries
            == {}
        )
        return
    np.testing.assert_array_equal(
        tifffile.imread(tmp_path / "images/exports/A01_s001_w2_z001_t001.tif"), pixels
    )
    assert subdirectory[FIELDS.IMAGE_FILES] == [
        "images/exports/A01_s001_w2_z001_t001.tif"
    ]
    entries = VirtualWorkspaceSourceProjectionEntries.from_subdirectory(
        subdirectory
    ).entries
    raster = entries["images/exports/A01_s001_w2_z001_t001.tif"]
    assert raster.source_alias == "RasterField"
    assert raster.image_metadata.source_voxel_spacing.values_zyx == (0.65, 0.65)
    assert (
        raster.image_metadata.source_voxel_spacing.native_coordinate_unit
        == "micrometer"
    )


def _stream_batch_sources(projections):
    plan = function_step_plan("StreamOwned")
    arrays = [np.full((2, 3), index, dtype=np.float32) for index in range(len(projections))]
    paths = [str(plan.output_dir / f"A01_s1_w{index}.tif") for index in range(len(projections))]
    records = tuple(
        ProducedOutputSemantics.from_output(
            plan,
            path,
            FunctionOutputIdentity(
                component_values={"well": "A01", "site": "1", "channel": str(index)},
                extension=".tif",
                source="stream source",
            ),
            output_context=AlignedImageSliceContext.main_flow(
                output_key=f"image-{index}", projection_key=projection,
                artifact_kind=ImageArtifactType.value,
            ),
        )
        for index, (path, projection) in enumerate(zip(paths, projections, strict=True))
    )
    return arrays, paths, records


def test_stream_batch_owns_correlated_projection_order_and_frozen_input_lists(monkeypatch):
    arrays, paths, records = _stream_batch_sources(("second", "first", "second", "first"))
    expected_arrays, expected_paths = tuple(arrays), tuple(paths)
    observed = []
    original_project = StreamOutputBatch.project_item

    def project(request):
        observed.append(request.source_description)
        arrays.clear()
        paths.clear()
        return original_project(request)

    monkeypatch.setattr(StreamOutputBatch, "project_item", staticmethod(project))
    batches = StreamOutputBatch.from_projection_groups(
        parser=ImageXpressFilenameParser(), payloads=arrays, paths=paths,
        produced_outputs=records,
    )
    assert observed == [expected_paths[index] for index in (0, 2, 1, 3)]
    assert len(batches) == 2
    assert [item.output_path for batch in batches for item in batch.items] == observed
    assert [item.producer_identity for batch in batches for item in batch.items] == [
        records[index].producer_identity for index in (0, 2, 1, 3)
    ]
    for item, index in zip(
        (item for batch in batches for item in batch.items), (0, 2, 1, 3), strict=True,
    ):
        assert item.data is expected_arrays[index]
        assert item.source_component_metadata["channel"] == str(index)


def test_stream_batch_keeps_first_projection_error_and_prior_callback_effects(monkeypatch):
    arrays, paths, records = _stream_batch_sources(("first", "second", "first", "second"))
    observed = []
    failure = ValueError("actual projector failure")
    original_project = StreamOutputBatch.project_item

    def project(request):
        observed.append(request.source_description)
        if request.source_description == paths[1]:
            raise failure
        return original_project(request)

    monkeypatch.setattr(StreamOutputBatch, "project_item", staticmethod(project))
    with pytest.raises(ValueError) as raised:
        StreamOutputBatch.from_projection_groups(
            parser=ImageXpressFilenameParser(), payloads=arrays, paths=paths,
            produced_outputs=records,
        )
    assert raised.value is failure
    assert observed == [paths[index] for index in (0, 2, 1)]


def test_stream_batch_validates_cardinality_and_routes_before_projecting(monkeypatch):
    arrays, paths, records = _stream_batch_sources(("first", "second"))

    def forbidden_project(request):
        raise AssertionError("invalid inputs reached projection")

    monkeypatch.setattr(StreamOutputBatch, "project_item", staticmethod(forbidden_project))
    parser = ImageXpressFilenameParser()
    with pytest.raises(ValueError, match="payload/path cardinality mismatch"):
        StreamOutputBatch.from_projection_groups(
            parser=parser, payloads=arrays, paths=paths[:1], produced_outputs=(),
        )
    with pytest.raises(ValueError, match="payload/output-record cardinality mismatch"):
        StreamOutputBatch.from_projection_groups(
            parser=parser, payloads=arrays, paths=paths, produced_outputs=records[:1],
        )
    with pytest.raises(ValueError, match="at least one produced output record"):
        StreamOutputBatch.from_projection_groups(
            parser=parser, payloads=(), paths=(), produced_outputs=(),
        )
    with pytest.raises(ValueError, match="cannot mix producer projections"):
        StreamOutputBatch.from_projection(
            parser=parser, payloads=arrays, paths=paths, produced_outputs=records,
        )
