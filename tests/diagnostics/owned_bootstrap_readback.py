"""Read-only exact synthetic publication checks on original OpenHCS owners."""

from collections import Counter
from csv import DictReader
import json
from pathlib import Path

import numpy as np

from openhcs.agent.dto.execution import ArtifactPlanInspection
from openhcs.constants import AllComponents
from openhcs.core.image_file_serialization import ImageFileFormat
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.core.source_matching import source_component_metadata_value
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
    selected = ((0, 1, 2), (2, 0), (2, 0))
    result = dict(axis_id=axis_id, reader_planes=to_jsonable(native), steps=[])
    expected_runtime_paths = set()
    expected_durable_images = set()
    expected_csv_paths = set()
    expected_roi_paths = set()
    for summary, indices in zip(inspection.steps, selected, strict=True):
        expected = pixels[list(indices)]
        expected_addresses = tuple(source_addresses[index] for index in indices)
        plans = {plan.name: plan for plan in summary.artifact_outputs}
        assert set(plans) == {'volume_fixture_image', 'volume_fixture_labels', 'volume_fixture_rows'}

        def record(name):
            plan = plans[name]
            [matched] = [item for item in records if item.key.name == plan.name and item.path == plan.path]
            expected_runtime_paths.add(matched.path)
            return matched

        image = record('volume_fixture_image').value.data
        labels = record('volume_fixture_labels').value.data
        rows = record('volume_fixture_rows').value.data
        np.testing.assert_array_equal(image_payload_data(image), expected)
        np.testing.assert_array_equal(object_label_dense_array(labels), expected.astype(np.int32))
        assert addresses(image_payload_metadata(image)) == expected_addresses
        assert addresses(image_payload_metadata(labels)) == expected_addresses
        assert rows.subject.object_name == plans['volume_fixture_labels'].name
        assert rows.subject.id_field == 'object_label'
        expected_rows = tuple((local, 11+source, (source+2)**2)
                              for local, source in enumerate(indices))
        actual_rows = tuple(zip(rows.rows.column_values('slice_index'),
                                rows.rows.column_values('object_label'),
                                rows.rows.column_values('pixel_count'), strict=True))
        assert actual_rows == expected_rows
        flow = summary.main_flow_materialization
        assert flow is not None and flow.backend == 'disk'
        output_dir = Path(flow.output_dir)
        saved = tuple(item for item in projections(Path(flow.plate_root))
                      if (Path(flow.plate_root)/item.ref.backend_address).is_relative_to(output_dir))
        assert len(saved) == len(indices), (output_dir, saved)
        assert {item.address for item in saved} == {native[index].address for index in indices}
        saved_images = []
        for projection in saved:
            [source] = [index for index in indices if native[index].address == projection.address]
            path = Path(flow.plate_root)/projection.ref.backend_address
            np.testing.assert_array_equal(ImageFileFormat.require_path(path).read(path), pixels[source])
            assert projection.image_metadata is not None
            assert addresses(projection.image_metadata) == (source_addresses[source],)
            expected_durable_images.add(path.resolve())
            saved_images.append(dict(path=str(path), address=to_jsonable(projection.address), source_plane=source))
        analysis = Path(plans['volume_fixture_rows'].materialization.analysis_output_dir)
        [csv_path] = list(analysis.glob(f'*_volume_fixture_rows_step{summary.step_index}_details.csv'))
        with csv_path.open(newline='') as stream:
            csv_rows = tuple((int(row['slice_index']), int(row['object_label']), int(row['pixel_count']))
                             for row in DictReader(stream))
        assert csv_rows == expected_rows
        expected_csv_paths.add(csv_path.resolve())
        roi_dir = Path(plans['volume_fixture_labels'].materialization.analysis_output_dir)
        zip_paths = list(roi_dir.glob(f'*_volume_fixture_labels_step{summary.step_index}*.zip'))
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
        result['steps'].append(dict(step_index=summary.step_index, source_planes=indices,
                                    runtime_shape=list(expected.shape), source_addresses=expected_addresses,
                                    images=saved_images, csv=dict(path=str(csv_path), rows=csv_rows),
                                    rois=roi_inventory))
    assert {item.path for item in records} == expected_runtime_paths
    actual_images = {path.resolve() for path in (owned/'outputs').rglob('*.tif')}
    assert actual_images == expected_durable_images, (actual_images, expected_durable_images)
    assert {path.resolve() for path in (owned/'outputs').rglob('*volume_fixture_rows*details.csv')} == expected_csv_paths
    assert {path.resolve() for path in (owned/'outputs').rglob('*volume_fixture_labels*.zip')} == expected_roi_paths
    result['omitted_controls'] = ['full three-plane reorder', 'singleton']
    return result
