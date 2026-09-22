"""Synthetic-plate integration coverage for 2D neurite outgrowth."""

import csv
import io
import json
import logging
from multiprocessing.shared_memory import SharedMemory
from pathlib import Path
import queue
import time
from contextlib import redirect_stderr, redirect_stdout

import openhcs  # noqa: F401 - prefer repository submodules before direct imports
import numpy as np
import tifffile
from objectstate import ObjectStateRegistry
from polystore.roi import PolylineShape, load_rois_from_zip
from polystore.napari_stream import NapariStreamingBackend
from polystore.streaming import (
    StreamingBatchMessageBuilder,
    StreamingBatchMessageRequest,
)
from polystore.streaming.identity import (
    FixedStreamProducerIdentityKind,
    StreamProducerIdentity,
)
from polystore.streaming.viewer_transport import (
    BatchViewerStreamSourceMetadata,
    ViewerStreamBackendKwargs,
    ViewerStreamProducer,
    ViewerStreamRequest,
    ViewerStreamSource,
    ViewerStreamSourceIdentity,
)
from zmqruntime.viewer_protocol import ViewerTransportEndpoint
from zmqruntime.config import TransportMode
from skimage.draw import disk, line

from objectstate.lazy_factory import ensure_global_config_context
from openhcs.constants import AllComponents, GroupBy, Microscope, VariableComponents
from openhcs.core.config import (
    AnalysisConsolidationConfig,
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyProcessingConfig,
    LazyVFSConfig,
    MaterializationBackend,
    NapariDisplayConfig,
    PathPlanningConfig,
    PipelineConfig,
    VFSConfig,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.artifacts import ObjectLabelsArtifactType
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.progress import ProgressEvent, set_progress_queue
from openhcs.core.progress.live_measurements import LiveMeasurementProgressPayload
from openhcs.core.steps import FunctionStep
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
)
from openhcs.processing.materialization.core import (
    Output,
    ViewerStreamBackendCallKwargs,
)
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    MetaXpressCellBodySettings,
    MetaXpressNuclearSettings,
    MetaXpressOutgrowthSettings,
    neurite_outgrowth_metaxpress,
)
from openhcs.demo.synthetic_data import (
    SyntheticMicroscopyGenerator,
)


def _write_known_neurite_images(plate_dir):
    neurites = np.zeros((96, 128), dtype=np.uint16)
    rows, columns = disk((48, 20), 9, shape=neurites.shape)
    neurites[rows, columns] = 1000
    rows, columns = line(48, 28, 48, 110)
    neurites[rows, columns] = 700
    rows, columns = line(48, 70, 25, 95)
    neurites[rows, columns] = 700

    nuclei = np.zeros_like(neurites)
    rows, columns = disk((48, 20), 5, shape=nuclei.shape)
    nuclei[rows, columns] = 1200

    image_dir = plate_dir / "TimePoint_1"
    for site in (1, 2):
        tifffile.imwrite(image_dir / f"A01_s{site:03d}_w1_z001_t001.tif", neurites)
        tifffile.imwrite(image_dir / f"A01_s{site:03d}_w2_z001_t001.tif", nuclei)
    return np.stack((neurites, nuclei))


def test_neurite_outgrowth_runs_on_synthetic_plate_as_2d_channel_stack(
    tmp_path, caplog, monkeypatch
):
    caplog.set_level(logging.CRITICAL)
    plate_dir = tmp_path / "synthetic_neurite_plate"
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        SyntheticMicroscopyGenerator(
            output_dir=str(plate_dir),
            grid_size=(1, 1),
            tile_size=(96, 128),
            overlap_percent=10,
            stage_error_px=1,
            wavelengths=2,
            z_stack_levels=1,
            num_cells=1,
            wells=["A01"],
            format="ImageXpress",
            random_seed=11,
        ).generate_dataset()
    source_stack = _write_known_neurite_images(plate_dir)

    suffix = "_neurite_test"
    vfs_config = VFSConfig(materialization_backend=MaterializationBackend.DISK)
    global_config = GlobalPipelineConfig(
        num_workers=1,
        microscope=Microscope.IMAGEXPRESS,
        use_threading=True,
        path_planning_config=PathPlanningConfig(output_dir_suffix=suffix),
        vfs_config=vfs_config,
        analysis_consolidation_config=AnalysisConsolidationConfig(enabled=False),
    )
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(output_dir_suffix=suffix),
        vfs_config=LazyVFSConfig.from_config(vfs_config),
    )
    step = FunctionStep(
        name="MetaXpress-style neurite outgrowth",
        func=(
            neurite_outgrowth_metaxpress,
            {
                "cell_body": MetaXpressCellBodySettings(
                    approximate_max_width=30.0,
                    minimum_area=100.0,
                    intensity_above_local_background=100.0,
                ),
                "outgrowth": MetaXpressOutgrowthSettings(
                    maximum_width=3.0,
                    intensity_above_local_background=100.0,
                    minimum_cell_growth_to_log_as_significant=20.0,
                ),
                "use_nuclear_stain": True,
                "nuclear_stain": MetaXpressNuclearSettings(
                    channel_index=1,
                    approx_min_width=6.0,
                    approx_max_width=14.0,
                    intensity_above_local_background=200.0,
                ),
            },
        ),
        processing_config=LazyProcessingConfig(
            variable_components=[VariableComponents.CHANNEL],
            group_by=GroupBy.SITE,
        ),
    )

    ObjectStateRegistry.clear()
    progress_queue = queue.Queue()
    dense_outputs = {}
    original_with_components = Output.with_variable_components

    def observe_dense_output(output, components):
        projected = original_with_components(output, components)
        if projected.path.endswith((".labels.tif", ".checkpoint.tif")):
            dense_outputs[projected.path] = projected
        return projected

    monkeypatch.setattr(Output, "with_variable_components", observe_dense_output)
    try:
        ensure_global_config_context(GlobalPipelineConfig, global_config)
        orchestrator = PipelineOrchestrator(
            plate_dir, pipeline_config=pipeline_config
        ).initialize()
        set_progress_queue(progress_queue)
        compilation = orchestrator.compile_pipelines(
            pipeline_definition=[step], well_filter=["A01"]
        )
        compiled_context = compilation.runtime_contexts["A01"]
        compiled_plan = compiled_context.step_plans[0]
        checkpoint_plan = next(
            output
            for output in compiled_plan.artifact_outputs.values()
            if output.name == "neurite_candidate_mask"
        )
        assert checkpoint_plan.group_component is AllComponents.SITE
        assert checkpoint_plan.group_scope_sources()
        assert checkpoint_plan.source_context_source() is None
        assert compiled_plan.variable_components == [VariableComponents.CHANNEL]
        assert compiled_plan.group_by is GroupBy.SITE
        compiled_pattern = compiled_plan.compiled_function_pattern
        assert compiled_pattern is not None
        compiled_invocation = next(compiled_pattern.iter_invocations())
        assert compiled_invocation.kwargs_dict["pixel_size"] == 0.65
        expected = CallableContract.from_callable(
            neurite_outgrowth_metaxpress
        ).resolve_raw_runtime_callable()(
            source_stack, **compiled_invocation.kwargs_dict
        )

        results = orchestrator.execute_compiled_plate(
            execution_bundle=compilation,
            progress_queue=progress_queue,
            progress_context={
                "execution_id": f"test::{time.time_ns()}",
                "plate_id": str(plate_dir),
                "axis_id": "",
            },
        )
        assert results["A01"].is_success(), results["A01"].error_message

        progress_events = []
        while True:
            try:
                progress_events.append(
                    ProgressEvent.from_dict(progress_queue.get_nowait())
                )
            except queue.Empty:
                break
        live_payloads = tuple(
            payload
            for event in progress_events
            for payload in (LiveMeasurementProgressPayload.from_context(event.context),)
            if payload is not None
        )
        materialized_measurement_locations = tuple(
            location
            for payload in live_payloads
            for preview in payload.previews
            for location in preview.materialized_locations
        )
        assert materialized_measurement_locations
        assert all(
            location.backend == "disk"
            for location in materialized_measurement_locations
        )
        assert all(
            Path(location.path).is_file()
            for location in materialized_measurement_locations
        )

        summary_paths = list(tmp_path.rglob("*neurite_outgrowth_summary*.csv"))
        cell_paths = list(tmp_path.rglob("*neurite_outgrowth_cells*.csv"))
        assert len(summary_paths) == 2
        assert len(cell_paths) == 2
        summary_rows = []
        for path in summary_paths:
            with path.open(newline="") as csv_file:
                rows = list(csv.DictReader(csv_file))
            assert len(rows) == 1
            summary_rows.extend(rows)
        cell_rows = []
        for path in cell_paths:
            with path.open(newline="") as csv_file:
                rows = list(csv.DictReader(csv_file))
            assert len(rows) == 1
            cell_rows.extend(rows)
        assert len(summary_rows) == 2
        assert len(cell_rows) == 2
        assert all(int(row["number_of_cells"]) == 1 for row in summary_rows)
        assert all(int(row["total_processes"]) == 1 for row in summary_rows)
        assert all(int(row["total_branches"]) == 1 for row in summary_rows)
        assert all(int(row["cell_body_channel_index"]) == 0 for row in summary_rows)
        assert all(int(row["nuclear_channel_index"]) == 1 for row in summary_rows)
        assert all(row["significant_growth"] == "True" for row in cell_rows)

        roi_paths = sorted(
            (
                *tmp_path.rglob("*cell_bodies*rois.roi.zip"),
                *tmp_path.rglob("*neurite_outgrowth*rois.roi.zip"),
                *tmp_path.rglob("*neurons*rois.roi.zip"),
                *tmp_path.rglob("*nuclei*rois.roi.zip"),
            )
        )
        assert len(roi_paths) == 8
        assert len([path for path in roi_paths if "cell_bodies" in path.name]) == 2
        assert (
            len(
                [path for path in roi_paths if "_neurite_outgrowth_step0_" in path.name]
            )
            == 2
        )
        assert len([path for path in roi_paths if "_neurons_step0_" in path.name]) == 2
        assert len([path for path in roi_paths if "nuclei" in path.name]) == 2
        assert all(
            "_w1_" in path.name for path in roi_paths if "nuclei" not in path.name
        )
        assert all("_w2_" in path.name for path in roi_paths if "nuclei" in path.name)
        assert all(load_rois_from_zip(path) for path in roi_paths)

        all_label_paths = []
        for artifact_name, expected_labels in zip(
            ("cell_bodies", "neurite_outgrowth", "neurons", "nuclei"),
            expected[3:7],
            strict=True,
        ):
            label_paths = tuple(tmp_path.rglob(f"*_{artifact_name}_step0.labels.tif"))
            assert len(label_paths) == 2
            all_label_paths.extend(label_paths)
            for label_path in label_paths:
                retained = tifffile.imread(label_path)
                assert retained.dtype == expected_labels.dtype
                np.testing.assert_array_equal(retained, expected_labels)

        checkpoint_paths = []
        for artifact_name, expected_checkpoint in zip(
            (
                "neurite_candidate_mask",
                "neurite_unrooted_residual",
                "neurite_secondary_ownership",
                "neurite_topology_dropped_trace",
                "neurite_topology_added_trace",
            ),
            expected[7:12],
            strict=True,
        ):
            paths = tuple(tmp_path.rglob(f"*_{artifact_name}.checkpoint.tif"))
            assert len(paths) == 2
            checkpoint_paths.extend(paths)
            for path in paths:
                retained = tifffile.imread(path)
                np.testing.assert_array_equal(
                    retained,
                    np.asarray(expected_checkpoint)[0],
                )
        assert len({path.name for path in checkpoint_paths}) == 10

        assert compiled_plan.output_plate_root is not None
        output_plate_root = Path(compiled_plan.output_plate_root)
        projected_label_paths = tuple(
            path for path in all_label_paths if path.is_relative_to(output_plate_root)
        )
        assert len(projected_label_paths) == 8
        metadata_path = output_plate_root / "openhcs_metadata.json"
        source_projection = VirtualWorkspaceSourceProjection.from_openhcs_metadata(
            output_plate_root,
            json.loads(metadata_path.read_text()),
        )
        for label_path in projected_label_paths:
            virtual_path = str(label_path.relative_to(output_plate_root))
            projection = source_projection.require_source_projection_for(
                VirtualWorkspacePathLookup.from_paths(
                    virtual_path,
                    str(label_path),
                )
            )
            assert projection.artifact_kind is ObjectLabelsArtifactType
            assert projection.address is None
            assert projection.execution_scope is not None
            assert projection.image_metadata is not None
            assert (
                projection.image_metadata.plane_axis is RuntimePlaneAxis.RUNTIME_SLICE
            )
            assert projection.image_metadata.source_provenance.source_plane_count == 2

            # Exercise the real stream projection of the compiled writer outputs.
            # Artifact storage axes are legitimately empty; source image planes are not.
            assert len(dense_outputs) == 18
        stream_kwargs = ViewerStreamBackendCallKwargs(
            ViewerStreamBackendKwargs(
                ViewerStreamRequest(
                    viewer_transport=ViewerTransportEndpoint(
                        host="localhost", port=5555, transport_mode=TransportMode.IPC
                    ),
                    display_config=NapariDisplayConfig(),
                    source=ViewerStreamSource(
                        identity=ViewerStreamSourceIdentity(
                            microscope_handler=compiled_context.microscope_handler,
                            plate_path=str(plate_dir),
                        ),
                        metadata=BatchViewerStreamSourceMetadata({}),
                    ),
                    producer=ViewerStreamProducer.from_identity(
                        StreamProducerIdentity.fixed_output(
                            FixedStreamProducerIdentityKind.DIRECT,
                            "synthetic-retained-domain",
                        )
                    ),
                )
            )
        )
        backend = NapariStreamingBackend()
        try:
            for outputs, kwargs in stream_kwargs.filemanager_batches(
                tuple(dense_outputs.values())
            ):
                request = kwargs["stream_request"]
                checkpoint_batch = all(
                    output.path.endswith(".checkpoint.tif") for output in outputs
                )
                if checkpoint_batch:
                    assert "plane_component_values" not in request.source.item_fields
                    assert all(
                        request.source.metadata.component_metadata_for_item(
                            output.path, 0
                        )["channel"]
                        == 1
                        for output in outputs
                    )
                else:
                    assert request.source.item_fields["plane_component_values"] == {
                        "channel": ["1", "2"]
                    }
                batch = StreamingBatchMessageBuilder.build(
                    backend,
                    StreamingBatchMessageRequest(
                        data_list=[output.content for output in outputs],
                        file_paths=[output.path for output in outputs],
                        stream_request=request,
                        component_names_request=backend.component_names_request(
                            request
                        ),
                        display_payload_extra=backend.display_payload_extra(request),
                    ),
                )
                for output, item in zip(outputs, batch.batch_images, strict=True):
                    assert output.variable_components == ()
                    # This fixture injects physical pixel_size into the callable,
                    # but does not declare voxel spacing on its runtime images.
                    assert output.metadata.source_voxel_spacing == SourceVoxelSpacing()
                    if checkpoint_batch:
                        assert "_w1_" in Path(output.path).name
                    else:
                        assert item["plane_component_values"] == {"channel": ["1", "2"]}
                        assert (
                            "channel"
                            not in request.source.metadata.component_metadata_for_item(
                                output.path, 0
                            )
                        )
                    memory = SharedMemory(name=item["shm_name"])
                    try:
                        transmitted = np.ndarray(
                            item["shape"], dtype=item["dtype"], buffer=memory.buf
                        ).copy()
                    finally:
                        memory.close()
                    np.testing.assert_array_equal(transmitted, output.content)
                    np.testing.assert_array_equal(
                        transmitted, tifffile.imread(output.path)
                    )
        finally:
            backend.cleanup()

        swc_paths = sorted(tmp_path.rglob("*neurite_morphology*.swc"))
        graph_roi_paths = sorted(tmp_path.rglob("*neurite_morphology*.graph.roi.zip"))
        assert len(swc_paths) == 2
        assert len(graph_roi_paths) == 2
        assert all(
            "# OpenHCS spatial graph: neurite_morphology" in path.read_text()
            for path in swc_paths
        )
        for graph_roi_path in graph_roi_paths:
            branch_rois = load_rois_from_zip(graph_roi_path)
            assert branch_rois
            for branch_roi in branch_rois:
                assert len(branch_roi.shapes) == 1
                assert isinstance(branch_roi.shapes[0], PolylineShape)
                assert branch_roi.metadata["label"] == 1
                assert branch_roi.metadata["neuron_label"] == 1
                assert branch_roi.metadata["branch_distance_um"] > 0
                assert branch_roi.metadata["euclidean_distance_um"] > 0
                assert branch_roi.metadata["tortuosity"] >= 1.0
                assert branch_roi.metadata["distance_from_soma_um"] >= 0
                assert "branch_type" in branch_roi.metadata

        summaries = sorted(
            (
                *tmp_path.rglob("*cell_bodies*segmentation_summary.txt"),
                *tmp_path.rglob("*neurite_outgrowth*segmentation_summary.txt"),
                *tmp_path.rglob("*neurons*segmentation_summary.txt"),
                *tmp_path.rglob("*nuclei*segmentation_summary.txt"),
            )
        )
        assert len(summaries) == 8
        assert all("Spatial dimensions: 2D" in path.read_text() for path in summaries)
    finally:
        set_progress_queue(None)
        ObjectStateRegistry.clear()
