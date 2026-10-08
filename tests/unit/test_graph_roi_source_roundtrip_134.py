"""Receiving #134: actual graph context/writer/ZIP, without a native process."""

from openhcs.core.artifacts import ImageArtifactType

from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import load_rois_from_zip

from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ArtifactSpec,
    ObjectArtifactMemberSubjectRelation,
    ObjectArtifactSubjectBinding,
    ObjectLabelsArtifactType,
    SpatialGraphArtifactType,
)
from openhcs.core.config import NapariStreamingConfig
from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_spatial_graph import (
    SpatialGraph,
    SpatialGraphEdge,
    SpatialGraphNode,
)
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_bindings import CompiledSourceBindingPlan
from openhcs.core.source_image_provenance import SourceImageProvenance
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelVariantData,
)
from openhcs.core.source_metadata import SourceVoxelSpacing

from openhcs.core.viewer_streaming_service import RoiStreamingRequest, StreamingService
from openhcs.processing.materialization import (
    MaterializationSpec,
    SpatialGraphROIOptions,
    ROIOptions,
    materialization_outputs,
    materialize,
)

@pytest.fixture(autouse=True)
def no_optional_storage_bootstrap(monkeypatch):
    import polystore.base

    monkeypatch.setattr(
        polystore.base,
        "ensure_storage_registry",
        lambda: pytest.fail("Provider/bootstrap execution is forbidden in this test"),
    )


class ProjectionAudit:
    """Independent capability exercises cooperative construction and projection."""

    def __init__(self, **kwargs):
        self.projection_events = []
        super().__init__(**kwargs)

    def contextualized_source_metadata(self, metadata):
        self.projection_events.append("before")
        result = super().contextualized_source_metadata(metadata)
        self.projection_events.append("after")
        return result


class AuditedGraph(ProjectionAudit, SpatialGraph):
    """New declaration; no writer, context strategy or reader registration."""


def graph_and_plan(*, plane, graph_type=SpatialGraph, extra_features=None):
    nodes = tuple(
        SpatialGraphNode(index + 1, coordinate)
        for index, coordinate in enumerate(((2.25, 3.5), (5.25, 9.5), (7.25, 12.5)))
    )
    edges = tuple(
        SpatialGraphEdge.from_features(
            edge_id=index + 1,
            source=nodes[index],
            target=nodes[index + 1],
            coordinates=np.asarray(
                (nodes[index].coordinates, nodes[index + 1].coordinates)
            ),
            features={
                "neuron_label": 7,
                "branch_distance_um": 8.5,
                **(extra_features or {}),
            },
        )
        for index in range(2)
    )
    graph = graph_type(
        name="declared_graph",
        nodes=nodes,
        edges=edges,
        coordinate_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
        source_plane_index=plane,
    )
    neurons = ArtifactSpec.output("neurons", ObjectLabelsArtifactType)
    plan = ArtifactOutputPlan(
        name=graph.name,
        path="/engineering/graph.pkl",
        artifact_type=SpatialGraphArtifactType,
        relations=(
            ObjectArtifactMemberSubjectRelation(
                source=neurons.ref(), member_id_field="neuron_label"
            ),
        ),
        producer_step_index=4,
        producer_step_scope_id="engineering-step",
    )
    return graph, plan


def contextualize(graph, plan, *, site=1):
    metadata = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/engineering/nuclear.tif", "/engineering/body.tif"),
            component_metadata=tuple(
                {
                    "well": "A01",
                    "site": site,
                    "channel": channel,
                    "z_index": 1,
                    "timepoint": 1,
                }
                for channel in (1, 2)
            ),
        ),
        source_image_names=("nuclear", "body"),
        source_voxel_spacing=graph.coordinate_spacing,
    )
    source = metadata.payload_with(np.zeros((2, 16, 16), dtype=np.uint8))
    result = (ImageArtifactType if plan is None else plan.artifact_type).contextualize_output(
        source, graph, plan, None
    )
    assert result.source_provenance == metadata.source_provenance.for_source_plane(
        graph.source_plane_index
    )
    return result


def save_graph(tmp_path, graph, plan):
    manager = FileManager({"disk": DiskStorageBackend()})
    path = materialize(
        MaterializationSpec(SpatialGraphROIOptions()),
        data=graph,
        path=str(tmp_path / "misleading_w99_z999.roi.zip"),
        filemanager=manager,
        backends=["disk"],
        backend_kwargs={},
        output_plan=plan,
    )
    return Path(path), load_rois_from_zip(Path(path))


@pytest.mark.parametrize("plane", [0, 1])
def test_declared_source_plane_survives_graph_writer_zip_and_subject_features(
    tmp_path, plane
):
    graph, plan = graph_and_plan(plane=plane)
    graph = contextualize(graph, plan)
    (output,) = materialization_outputs(
        MaterializationSpec(SpatialGraphROIOptions()),
        data=graph,
        path=str(tmp_path / "graph.roi.zip"),
        filemanager=FileManager({"disk": DiskStorageBackend()}),
        output_plan=plan,
    )
    path, restored = save_graph(tmp_path, graph, plan)
    metadata = ROIArchiveSourceMetadata.decode(restored)
    assert metadata is not None, "Native graph ZIP lost its existing source declaration"
    assert output.metadata.source_provenance == graph.source_provenance
    assert metadata.source_provenance == graph.source_provenance
    assert (
        metadata.source_path
        == ("/engineering/nuclear.tif", "/engineering/body.tif")[plane]
    )
    assert metadata.source_component_metadata["channel"] == plane + 1
    assert metadata.source_voxel_spacing == graph.source_voxel_spacing
    assert metadata.plane_axis is None
    assert metadata.source_spatial_domain == output.metadata.source_spatial_domain
    assert path.name == "misleading_w99_z999.graph.roi.zip"
    geometry = ROIArchiveSourceMetadata.geometry(restored)
    assert len(geometry) == len(graph.edges)
    for roi, edge in zip(geometry, graph.edges, strict=True):
        np.testing.assert_array_equal(roi.shapes[0].coordinates, edge.coordinates)
        assert roi.metadata["edge_id"] == edge.edge_id
        assert roi.metadata["source_node_id"] == edge.source_node_id
        assert roi.metadata["target_node_id"] == edge.target_node_id
        assert roi.metadata["neuron_label"] == 7
        assert roi.metadata["branch_distance_um"] == 8.5
        assert roi.metadata[ObjectArtifactSubjectBinding.SUBJECT_ID_FEATURE] == 7
        assert (
            '"object_labels","neurons","engineering-step",4'
            in roi.metadata[ObjectArtifactSubjectBinding.SUBJECT_FEATURE]
        )
        assert ROIArchiveSourceMetadata.FIELD not in roi.metadata
    assert (
        len(
            {
                roi.metadata[ObjectArtifactSubjectBinding.SUBJECT_FEATURE]
                for roi in geometry
            }
        )
        == 1
    )


def test_independent_graph_capability_and_new_feature_need_no_consumers(tmp_path):
    original, plan = graph_and_plan(
        plane=1,
        graph_type=AuditedGraph,
        extra_features={"engineering_confidence": 0.375},
    )
    graph = contextualize(original, plan)
    assert original.projection_events == ["before", "after"]
    assert (
        graph.projection_events == []
    )  # cooperative constructor for contextualized copy
    _, restored = save_graph(tmp_path, graph, plan)
    metadata = ROIArchiveSourceMetadata.decode(restored)
    assert metadata is not None, "New graph declaration lost its source declaration"
    assert metadata.source_provenance == graph.source_provenance
    assert all(roi.metadata["engineering_confidence"] == 0.375 for roi in restored)
    assert all(
        ROIArchiveSourceMetadata.FIELD not in roi.metadata
        for roi in ROIArchiveSourceMetadata.geometry(restored)
    )


@pytest.mark.parametrize("compiled_stack", [False, True])
def test_original_source_scope_separates_sites_and_links_label_and_graph_zip(
    tmp_path, compiled_stack
):
    """Artifact filenames do not own either grouping or field identity."""
    manager = FileManager({"disk": DiskStorageBackend()})
    context = (
        SimpleNamespace(
            microscope_handler=None,
            step_plans={
                4: CompiledStepPlan(
                    step_index=4,
                    step_name="neurite",
                    step_type="FunctionStep",
                    axis_id="A01",
                    variable_components=(VariableComponents.CHANNEL,),
                    group_by=GroupBy.SITE,
                )
            }
        )
        if compiled_stack
        else None
    )
    subject_tokens = []
    for site in (1, 2):
        original, graph_plan = graph_and_plan(plane=1)
        graph = contextualize(original, graph_plan, site=site)
        labels = np.zeros((16, 16), dtype=np.uint16)
        labels[2:6, 3:7] = 7
        body = ObjectLabelPayload(
            variant_data=ObjectLabelVariantData(labels=labels),
            source_provenance=graph.source_provenance,
        )
        body_plan = ArtifactOutputPlan(
            name="cell_bodies",
            path="/engineering/body.pkl",
            artifact_type=ObjectLabelsArtifactType,
            relations=(
                ObjectArtifactMemberSubjectRelation(
                    source=graph_plan.object_subject_binding().source,
                ),
            ),
            producer_step_index=graph_plan.producer_step_index,
            producer_step_scope_id=graph_plan.producer_step_scope_id,
        )
        archives = []
        for data, plan, options, filename in (
            (graph, graph_plan, SpatialGraphROIOptions(), "unrelated_graph"),
            (body, body_plan, ROIOptions(min_area=1), "unrelated_body"),
        ):
            path = materialize(
                MaterializationSpec(options),
                data,
                str(tmp_path / str(site) / filename),
                manager,
                ["disk"],
                context=context,
                pipeline_position=4,
                output_plan=plan,
            )
            archives.append(load_rois_from_zip(Path(path)))
        graph_rois, body_rois = archives
        token = graph_rois[0].metadata[ObjectArtifactSubjectBinding.SUBJECT_FEATURE]
        assert all(
            roi.metadata[ObjectArtifactSubjectBinding.SUBJECT_FEATURE] == token
            for rois in archives
            for roi in rois
        )
        assert all(
            roi.metadata[ObjectArtifactSubjectBinding.SUBJECT_ID_FEATURE] == 7
            for rois in archives
            for roi in rois
        )
        assert [roi.metadata["edge_id"] for roi in graph_rois] == [1, 2]
        assert len(body_rois) == 1
        subject_tokens.append(token)
    assert subject_tokens[0] != subject_tokens[1]


@pytest.mark.parametrize("named_planes", [False, True])
def test_compiled_source_plane_members_share_subject_without_merging_site_groups(
    named_planes,
):
    from openhcs.processing.materialization.core import MaterializationContext

    original, plan = graph_and_plan(plane=0)
    context = SimpleNamespace(
        step_plans={
            4: CompiledStepPlan(
                step_index=4,
                step_name="neurite",
                step_type="FunctionStep",
                axis_id="A01",
                source_binding_plan=CompiledSourceBindingPlan(
                    source_stack_components=(
                        (AllComponents.CHANNEL,) if named_planes else ()
                    ),
                ),
                variable_components=(
                    () if named_planes else (VariableComponents.CHANNEL,)
                ),
                group_by=GroupBy.SITE,
            )
        }
    )
    writer = MaterializationContext(
        base_path="/engineering/irrelevant-name",
        backends=[],
        backend_kwargs={},
        filemanager=FileManager({"disk": DiskStorageBackend()}),
        extra_inputs={},
        context=context,
        pipeline_position=4,
        output_plan=plan,
    )
    tokens = {}
    for site in (1, 2):
        for channel in (1, 2):
            tokens[site, channel] = writer.object_subject_metadata(
                {"neuron_label": 7},
                ImagePayloadMetadata(
                    source_component_metadata={
                        "well": "A01",
                        "site": site,
                        "channel": channel,
                    }
                ),
            )[ObjectArtifactSubjectBinding.SUBJECT_FEATURE]
    assert tokens[1, 1] == tokens[1, 2]
    assert tokens[2, 1] == tokens[2, 2]
    assert tokens[1, 1] != tokens[2, 1]


@pytest.mark.parametrize("sites", [(), (1, 2), (1, None)])
def test_object_subject_refuses_missing_or_ambiguous_source_domain(sites):
    _, plan = graph_and_plan(plane=0)
    provenance = SourceImageProvenance(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(None for _ in sites),
            component_metadata=tuple(
                None if site is None else {"well": "A01", "site": site}
                for site in sites
            ),
        ),
    )
    with pytest.raises(ValueError, match="one positively identified source"):
        plan.object_subject_binding().subject_token(
            producer_step_scope_id=plan.producer_step_scope_id,
            producer_step_index=plan.producer_step_index,
            source_provenance=provenance,
            identity_policy=SourceImageSetIdentityPolicy(),
        )


@pytest.mark.parametrize("invalid", ["absent", "unbound", "mixed", "conflicting"])
def test_original_native_admission_refuses_bad_graph_sources_before_transport(
    tmp_path, invalid
):
    graph, plan = graph_and_plan(plane=1)
    graph = contextualize(graph, plan)
    path, rois = save_graph(tmp_path, graph, plan)
    geometry = ROIArchiveSourceMetadata.geometry(rois)
    metadata = ImagePayloadMetadata(source_provenance=graph.source_provenance)
    bad_archives = {
        "absent": geometry,
        "unbound": ROIArchiveSourceMetadata.bind(geometry, ImagePayloadMetadata()),
        "mixed": [
            ROIArchiveSourceMetadata.bind(geometry[:1], metadata)[0],
            geometry[1],
        ],
        "conflicting": [
            ROIArchiveSourceMetadata.bind(geometry[:1], metadata)[0],
            ROIArchiveSourceMetadata.bind(
                geometry[1:],
                metadata.replace_fields(source_path="/engineering/other.tif"),
            )[0],
        ],
    }
    DiskStorageBackend().save(bad_archives[invalid], path)
    # No viewer/handler object: original source admission must reject before using either.
    service = StreamingService(
        FileManager({"disk": DiskStorageBackend()}), None, tmp_path
    )
    with pytest.raises(
        ValueError, match="Native ROI source metadata|missing or conflicting"
    ):
        service.stream_rois(
            RoiStreamingRequest(
                viewer=None,
                config=NapariStreamingConfig(enabled=True),
                status_callback=lambda _: None,
                error_callback=lambda error: pytest.fail(error),
                roi_filenames=(path.name,),
                require_source_metadata=True,
            )
        )
