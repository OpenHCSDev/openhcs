"""Contributor scope and saved producer addresses survive their real consumers."""

from dataclasses import dataclass, replace
from pathlib import Path
import pickle

import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType, MeasurementsArtifactType
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.orchestrator.execution_result import (
    RuntimeContextObservation, RuntimeExecutionObservation,
)
from openhcs.core.projected_image_output import SourceProjectedImageOutput
from openhcs.core.runtime_artifact_values import ArtifactKey, RuntimeValue
from openhcs.core.runtime_exports import (
    RuntimeExportExpectation, RuntimeExportObservation, runtime_export_failures,
)
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_metadata
from openhcs.core.runtime_measurements import MeasurementScope, MeasurementSubject, MeasurementTable
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis, RuntimePlaneAxisValueProjection
from openhcs.core.runtime_stores import (
    RuntimeArtifactAddress, RuntimeArtifactLocation, RuntimeValueStore,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_image_provenance import (
    RuntimeSourceImageProvenancePlane, SourceImageIdentity, SourceImageProvenancePlanes,
)
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.steps.abstract import StepExecutionObservation
from openhcs.processing.materialization import CsvOptions, MaterializationSpec
from openhcs.processing.materialization.core import Output, materialization_outputs
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from test_materialization_core import _viewer_stream_backend_kwargs


def _source(sites):
    return ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_voxel_spacing=SourceVoxelSpacing((0.5, 0.5)),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(f"/input/field_{i}.tif" for i in range(len(sites))),
            component_metadata=tuple(
                {"well": "A01", "channel": 2, "z_index": 1, "timepoint": 1,
                 **({"site": site} if site is not None else {})}
                for site in sites
            ),
        ),
    ).payload_with(np.arange(len(sites) * 12, dtype=np.uint16).reshape(len(sites), 3, 4))


class ProjectionAudit:
    def resolve_source_context(self, source, projection):
        self.calls.append("before")
        result = super().resolve_source_context(source, projection)
        self.calls.append("after")
        return result


class ReducedDeclaration(SourceProjectedImageOutput):
    def resolve_source_context(self, source, projection):
        assert projection.axis_size == source.shape[0]
        return image_payload_metadata(source).collapse_leading_plane_axis().payload_with(self.data)


@dataclass(frozen=True)
class DeclaredReducedField(ProjectionAudit, ReducedDeclaration):
    data: np.ndarray
    calls: list

    def with_data(self, data):
        return replace(self, data=data)


def test_mixed_acquired_and_reduced_batch_uses_distinct_original_display_scopes():
    source = _source((1, 3))
    declaration = DeclaredReducedField(np.full((3, 4), 720, dtype=np.uint16), [])
    reduced = ImageArtifactType.contextualize_output(
        source, declaration, None,
        RuntimePlaneAxisValueProjection.preserve(axis=RuntimePlaneAxis.SOURCE_BINDING, axis_size=2),
    )
    assert declaration.calls == ["before", "after"]
    acquired_metadata = image_payload_metadata(source).for_leading_source_plane(0)
    acquired = Output("acquired.tif", np.asarray(source)[0], acquired_metadata)
    aggregate = Output("reduced.tif", np.asarray(reduced), image_payload_metadata(reduced))
    adapter = _viewer_stream_backend_kwargs()
    batches = adapter.filemanager_batches((acquired, aggregate))
    assert len(batches) == 2
    for output, (outputs, kwargs) in zip((acquired, aggregate), batches, strict=True):
        assert outputs == (output,)
        request = kwargs["stream_request"]
        single = adapter.to_filemanager_kwargs(output)["stream_request"]
        assert request.display_config == single.display_config
        assert request.source.metadata.component_metadata_for_item(output.path, 0) == single.source.metadata.component_metadata_for_item(output.path, 0)
        assert request.producer == adapter.values.stream_request.producer
        assert request.viewer_transport == adapter.values.stream_request.viewer_transport
        assert request.display_config.component_modes() == adapter.values.stream_request.display_config.component_modes()
        assert output.metadata.source_voxel_spacing == SourceVoxelSpacing((0.5, 0.5))
    acquired_request, reduced_request = (kwargs["stream_request"] for _, kwargs in batches)
    assert "site" in acquired_request.display_config.COMPONENT_ORDER
    assert "site" not in reduced_request.display_config.COMPONENT_ORDER
    assert aggregate.metadata.source_provenance.source_image_provenance_planes.contributor_count == 2
    np.testing.assert_array_equal(aggregate.content, declaration.data)


@pytest.mark.parametrize("sites", ((), (None,), (1,), (1, 1), (1, None), (None, None)))
def test_absence_one_equal_or_incomplete_contributors_cannot_exempt_acquired_plane(sites):
    metadata = image_payload_metadata(_source(sites)).collapse_leading_plane_axis()
    components = {
        "well": "A01", "channel": 2, "z_index": 1, "timepoint": 1,
    }
    # Explicitly absent scalar identity, not a selected plane with a valid common site.
    metadata = ImagePayloadMetadata(
        source_component_metadata=components,
        source_image_provenance_planes=SourceImageProvenancePlanes((
            RuntimeSourceImageProvenancePlane(
                SourceImageIdentity(component_metadata=components),
                contributors=metadata.source_image_provenance_planes.contributors,
            ),
        )),
    )
    output = Output("unaddressed.tif", np.zeros((3, 4), dtype=np.uint16), metadata)
    adapter = _viewer_stream_backend_kwargs()
    assert "site" in metadata.source_provenance.required_scalar_components(("site",))
    with pytest.raises(ValueError, match="site"):
        adapter.to_filemanager_kwargs(output)
    with pytest.raises(ValueError, match="site"):
        adapter.filemanager_batches((output,))


def test_present_scalar_override_remains_required_despite_varied_contributors():
    metadata = image_payload_metadata(_source((1, 3))).collapse_leading_plane_axis()
    metadata = metadata.replace_fields(source_component_metadata={
        "well": "A01", "site": 7, "channel": 2, "z_index": 1, "timepoint": 1,
    })
    assert metadata.source_provenance.required_scalar_components(("site",)) == ("site",)
    output = Output("override.tif", np.zeros((3, 4), dtype=np.uint16), metadata)
    request = _viewer_stream_backend_kwargs().to_filemanager_kwargs(output)["stream_request"]
    assert "site" in request.display_config.COMPONENT_ORDER
    assert request.source.metadata.component_metadata_for_item(output.path, 0)["site"] == 7


def _saved_table(tmp_path, *, producer, fields):
    table = MeasurementTable(
        name="Cells", subject=MeasurementSubject(MeasurementScope.ARTIFACT, "Cells"),
        rows=MeasurementSparseColumnarRows.from_rows(
            ({field: 1 for field in fields},), fields=tuple(FieldSpec(field) for field in fields),
        ),
    )
    store = RuntimeValueStore()
    record = store.record(RuntimeValue(
        key=ArtifactKey(name="Cells", artifact_type=MeasurementsArtifactType,
                        scope=RuntimeExecutionAxisScope(axis_id="A01")),
        data=table,
    ), path=f"/runtime/{producer}/Cells", backend="memory")
    filemanager = FileManager({"memory": MemoryStorageBackend()})
    outputs = materialization_outputs(
        MaterializationSpec(CsvOptions(filename_suffix=".csv")), table,
        str(tmp_path / f"Cells_{producer}"), filemanager,
    )
    for output in outputs:
        # Persist exactly the original writer's content and declared path.
        Path(output.path).write_text(output.require_text_content(), encoding="utf-8")
    observation = StepExecutionObservation(
        {RuntimeArtifactAddress.from_record(record): tuple(RuntimeArtifactLocation(output.path, "disk") for output in outputs)},
        tuple(Path(output.path) for output in outputs),
    )
    return record, observation


def test_same_named_field_and_aggregate_tables_keep_exact_producer_ownership(tmp_path):
    acquired, acquired_outputs = _saved_table(tmp_path, producer="step1", fields=("site", "source_image_name"))
    aggregate, aggregate_outputs = _saved_table(tmp_path, producer="step3", fields=("area",))
    execution = RuntimeExecutionObservation((
        RuntimeContextObservation("A01", (acquired, aggregate), StepExecutionObservation.combine((acquired_outputs, aggregate_outputs))),
    ))
    transported = pickle.loads(pickle.dumps(execution))
    exports = RuntimeExportObservation.from_runtime_observations((transported,))
    spec = ArtifactSpec.output(name="Cells", artifact_type=MeasurementsArtifactType,
                               materialization=MaterializationSpec(CsvOptions(filename_suffix=".csv")))
    expectation = RuntimeExportExpectation.from_output_specs((spec,))
    assert exports.matching_table_outputs(acquired) == acquired_outputs.runtime_export_paths
    assert exports.matching_table_outputs(aggregate) == aggregate_outputs.runtime_export_paths
    assert runtime_export_failures(expectation, exports, {"A01": (acquired, aggregate)}) == ()
    # Files and a same-named neighbor cannot replace the missing producer relation.
    unowned = RuntimeExportObservation.from_output_paths(exports.output_files, outputs=aggregate_outputs)
    failures = runtime_export_failures(expectation, unowned, {"A01": (acquired, aggregate)})
    assert len(failures) == 1 and "no matching table output" in failures[0]
    # A correct address does not waive its own required columns.
    acquired_outputs.runtime_export_paths[0].write_text("area\n1\n", encoding="utf-8")
    invalid = RuntimeExportObservation.from_runtime_observations((transported,))
    failures = runtime_export_failures(expectation, invalid, {"A01": (acquired, aggregate)})
    assert any("site" in failure and "source_image_name" in failure for failure in failures)
