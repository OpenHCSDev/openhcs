"""Read-only exact synthetic publication checks on original OpenHCS owners."""

from collections import Counter
from csv import DictReader
import json
from pathlib import Path

import numpy as np

from openhcs.agent.dto.execution import ArtifactPlanInspection
from openhcs.constants import AllComponents
from openhcs.core.artifacts import ArtifactType, ImageArtifactType
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.core.source_bindings import SourceProjectionRole
from openhcs.core.source_projection import OpenHCSPlaneAddress
from openhcs.core.virtual_workspace_metadata import (
    METADATA_CONFIG, OpenHCSMetadataSubdirectories,
    VirtualWorkspaceSourceProjectionEntries,
)
from openhcs.runtime.zmq_execution_observation import ZMQRuntimeExecutionObservationExport
from openhcs.serialization.json import to_jsonable
from polystore.roi import load_rois_from_zip


def projections(plate: Path):
    metadata_path = METADATA_CONFIG.metadata_path(plate)
    metadata = OpenHCSMetadataSubdirectories(json.loads(metadata_path.read_text()))
    return tuple(
        projection
        for section in metadata.values()
        for projection in VirtualWorkspaceSourceProjectionEntries.from_subdirectory(section).entries.values()
    )


def addresses(metadata):
    return tuple(
        tuple(source_component_metadata_value(plane.component_metadata, component)
              for component in AllComponents)
        for plane in metadata.source_provenance.source_image_provenance_planes.planes
    )


def require_projection_inventory(saved, source_addresses, artifact_plans):
    """Require primary AND named image planes from the compiled declarations."""
    expected = Counter((SourceProjectionRole.PRIMARY_PLANE, None, ImageArtifactType, address)
                       for address in source_addresses)
    for plan in artifact_plans:
        artifact_type = ArtifactType.coerce(plan.kind)
        if (issubclass(artifact_type, ImageArtifactType) and plan.materialization is not None
                and plan.materialization.persistent_enabled):
            expected.update((SourceProjectionRole.SOURCE_ARTIFACT, plan.name, artifact_type, address)
                            for address in source_addresses)
    actual = Counter((item.projection_role, item.source_alias, item.artifact_kind, item.address)
                     for item in saved)
    assert actual == expected, (actual, expected)
    assert len({item.ref.backend_address for item in saved}) == sum(expected.values())


def require_csv_rows(csv_rows, expected_rows, source_addresses, object_name):
    """Decode each durable address through the original complete-address owner."""
    actual_rows = tuple((int(row['slice_index']), int(row['object_label']), int(row['pixel_count']))
                        for row in csv_rows)
    assert actual_rows == expected_rows
    for row, (local, _label, _area) in zip(csv_rows, expected_rows, strict=True):
        address = OpenHCSPlaneAddress.from_complete_source_metadata(row)
        assert address is not None and address == source_addresses[local], (row, source_addresses[local])
        assert row['object_name'] == object_name
    return actual_rows


def verify_volume_publication(owned: Path, image_path: Path, pixels: np.ndarray,
                              inspection: ArtifactPlanInspection) -> dict:
    """Require all declared runtime artifacts and persistent plane/row/ROI proofs."""
    observation = ZMQRuntimeExecutionObservationExport.read(owned/'observation.pkl.gz')
    observation.require_valid_observation()
    assert observation.axis_count == 1
    [axis_id] = observation.records_by_axis
    records = observation.records_by_axis[axis_id]
    native = sorted(projections(image_path.parent),
                    key=lambda item: int(item.address.value_for(AllComponents.Z_INDEX)))
    assert len(native) == 3
    assert all(item.image_metadata is not None for item in native)
    source_addresses = tuple(addresses(item.image_metadata)[0] for item in native)
    assert len(set(source_addresses)) == 3
    selected = tuple(indices for indices in ((0, 1, 2), (2, 0, 1), (2, 0), (0,)) for _ in range(3))
    result = dict(axis_id=axis_id, reader_planes=to_jsonable(native), steps=[])
    expected_runtime_paths = set()
    expected_durable_images = set()
    expected_csv_paths = set()
    expected_roi_paths = set()
    for summary, indices in zip(inspection.steps, selected, strict=True):
        expected = pixels[list(indices)]
        expected_addresses = tuple(source_addresses[index] for index in indices)
        plans = {plan.name: plan for plan in summary.artifact_outputs}
        image_name = ('selected_volume_fixture_v2' if summary.step_index % 3 == 0
                      else 'volume_fixture_image_v2')
        inspection_names = {'volume_fixture_image_v2', 'volume_fixture_labels_v2', 'volume_fixture_rows_v2'}
        assert set(plans) == ({image_name} if summary.step_index % 3 == 0 else inspection_names)

        def record(name):
            plan = plans[name]
            [matched] = [item for item in records if item.key.name == plan.name and item.path == plan.path]
            expected_runtime_paths.add(matched.path)
            return matched

        image = record(image_name).data
        np.testing.assert_array_equal(image_payload_data(image), expected)
        assert addresses(image_payload_metadata(image)) == expected_addresses
        flow = summary.main_flow_materialization
        assert flow is not None and flow.backend == 'disk'
        output_dir = Path(flow.output_dir)
        saved = tuple(item for item in projections(Path(flow.plate_root))
                      if (Path(flow.plate_root)/item.ref.backend_address).is_relative_to(output_dir))
        selected_addresses = tuple(native[index].address for index in indices)
        require_projection_inventory(saved, selected_addresses, summary.artifact_outputs)
        saved_images = []
        for projection in saved:
            [source] = [index for index in indices if native[index].address == projection.address]
            path = Path(flow.plate_root)/projection.ref.backend_address
            np.testing.assert_array_equal(ImageFileFormat.require_path(path).read(path), pixels[source])
            assert projection.image_metadata is not None
            assert addresses(projection.image_metadata) == (source_addresses[source],)
            expected_durable_images.add(path.resolve())
            saved_images.append(dict(path=str(path), address=to_jsonable(projection.address), source_plane=source))
        step_result = dict(step_index=summary.step_index, source_planes=indices,
                           runtime_shape=list(expected.shape), source_addresses=expected_addresses,
                           images=saved_images)
        result['steps'].append(step_result)
        if summary.step_index % 3 == 0:
            continue
        labels = record('volume_fixture_labels_v2').data
        rows = record('volume_fixture_rows_v2').data
        np.testing.assert_array_equal(object_label_dense_array(labels), expected.astype(np.int32))
        assert addresses(image_payload_metadata(labels)) == expected_addresses
        assert rows.subject.object_name == plans['volume_fixture_labels_v2'].name
        assert rows.subject.id_field == 'object_label'
        expected_rows = tuple((local, 11+source, (source+2)**2)
                              for local, source in enumerate(indices))
        actual_rows = tuple(zip(rows.rows.column_values('slice_index'),
                                rows.rows.column_values('object_label'),
                                rows.rows.column_values('pixel_count'), strict=True))
        assert actual_rows == expected_rows
        for component in AllComponents:
            assert tuple(str(value) for value in rows.rows.column_values(component.value)) == tuple(
                address.value_for(component) for address in selected_addresses)
        analysis = Path(plans['volume_fixture_rows_v2'].materialization.analysis_output_dir)
        [csv_path] = list(analysis.glob(f'*_volume_fixture_rows_v2_step{summary.step_index}_details.csv'))
        with csv_path.open(newline='') as stream:
            csv_rows = tuple(DictReader(stream))
        require_csv_rows(csv_rows, expected_rows, selected_addresses, rows.subject.object_name)
        expected_csv_paths.add(csv_path.resolve())
        roi_dir = Path(plans['volume_fixture_labels_v2'].materialization.analysis_output_dir)
        zip_paths = list(roi_dir.glob(f'*_volume_fixture_labels_v2_step{summary.step_index}*.zip'))
        assert zip_paths
        roi_inventory = []
        observed_source_labels = []
        for path in zip_paths:
            rois = load_rois_from_zip(path)
            metadata = ROIArchiveSourceMetadata.decode(rois)
            assert metadata is not None
            roi_addresses = addresses(metadata)
            assert roi_addresses and set(roi_addresses).issubset(expected_addresses)
            for roi in rois:
                label = int(roi.metadata['label'])
                [source] = [index for index in indices if label == 11+index]
                assert float(roi.metadata['area']) == (source+2)**2
                if metadata.source_provenance.source_plane_count == 1:
                    assert roi_addresses == (source_addresses[source],)
                else:
                    [local] = roi.metadata['plane_indices']
                    assert roi_addresses[local] == source_addresses[source]
                observed_source_labels.append((source, label))
            expected_roi_paths.add(path.resolve())
            roi_inventory.append(dict(path=str(path), metadata=to_jsonable(metadata),
                                      labels=[roi.metadata for roi in rois]))
        assert Counter(observed_source_labels) == Counter((source, 11+source) for source in indices)
        step_result.update(csv=dict(path=str(csv_path), rows=csv_rows), rois=roi_inventory)
    last = inspection.steps[-1]
    final_dir = Path(last.output_dir)
    flow = last.main_flow_materialization
    assert flow is not None
    if final_dir != Path(flow.output_dir):
        final = tuple(item for item in projections(Path(flow.plate_root))
                      if (Path(flow.plate_root)/item.ref.backend_address).is_relative_to(final_dir))
        require_projection_inventory(final, (native[0].address,), ())
        for projection in final:
            path = Path(flow.plate_root)/projection.ref.backend_address
            np.testing.assert_array_equal(ImageFileFormat.require_path(path).read(path), pixels[0])
            assert addresses(projection.image_metadata) == (source_addresses[0],)
            expected_durable_images.add(path.resolve())
        result['final_main_images'] = to_jsonable(final)
    assert {item.path for item in records} == expected_runtime_paths
    actual_images = {path.resolve() for path in (owned/'outputs').rglob('*.tif')}
    assert actual_images == expected_durable_images, (actual_images, expected_durable_images)
    assert {path.resolve() for path in (owned/'outputs').rglob('*volume_fixture_rows_v2*details.csv')} == expected_csv_paths
    assert {path.resolve() for path in (owned/'outputs').rglob('*volume_fixture_labels_v2*.zip')} == expected_roi_paths
    assert expected_csv_paths.issubset({path.resolve() for path in observation.exports.table_outputs})
    assert expected_roi_paths.issubset({path.resolve() for path in observation.exports.output_files})
    result['omitted_controls'] = []
    return result
