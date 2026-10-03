"""Original point writer -> stream metadata -> unchanged projection controls.

No compilation, viewer instance, native process or endpoint connection.
"""
from dataclasses import replace
from pathlib import Path

import numpy as np
import pytest
import tifffile
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import load_rois_from_zip
from polystore.roi_converters import NapariROIConverter
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming.viewer_transport import ViewerStreamProducer, ViewerStreamSourceIdentity
from polystore.streaming_constants import StreamingDataType
from zmqruntime.config import TransportMode
from zmqruntime.viewer_protocol import ViewerTransportEndpoint

from openhcs.constants.constants import VariableComponents
from openhcs.core.config import NapariStreamingConfig
from openhcs.core.memory import numpy as numpy_func
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.roi_point_metadata import ROIFractionalZ
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_measurements import (
    MeasurementScope, MeasurementSubject, MeasurementTable, ObjectCoreMeasurementFeature,
)
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import (
    OriginalSourceMetadata, SourceFilterPathMetadata, SourceVoxelSpacing,
)
from openhcs.core.steps.function_artifact_materialization import ArtifactStreamSourceMetadataAuthority
from openhcs.core.steps.stream_component_semantics import StreamComponentMessageExtraAuthority
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.streaming_config_factory import StreamingViewerRuntimeConfig, StreamingViewerSurface
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.processing.materialization import (
    CsvOptions, MaterializationSpec, PointROIOptions, materialization_outputs, materialize,
)
from openhcs.processing.materialization.core import PointROIOutput, ViewerStreamBackendCallKwargs
from openhcs.runtime.napari_streaming_handlers import NapariStreamLayerAddress, NapariStreamLayerItem
from openhcs.runtime.napari_viewer_server import NapariPointsLayerDisplayHandler
from openhcs.runtime.viewer_component_system import ViewerComponentValueDomainPayload


class SyntheticMicroscope:
    """Original filename parser only; no metadata or runtime service needed."""

    parser = SourceSchemaFilenameParser()


def point_fixture(root: Path, planes: int, origin: int, *, source_records=False):
    components = tuple(
        dict(well='A01', site=1, channel=1, z_index=origin + index, timepoint=1)
        for index in range(planes)
    )
    paths = tuple(str(root / f'A01_s001_w1_z{origin + index:03d}_t001.tif') for index in range(planes))
    if source_records:
        for component, path in zip(components, paths, strict=True):
            OriginalSourceMetadata.from_mapping({
                'well': 'A01', 'site': '001', 'channel': '1',
                'timepoint': '001', 'z_index': f"{component['z_index']:03d}",
            }).merge_into(component, path=path)
            SourceFilterPathMetadata.from_paths((Path(path).name, path)).merge_into(
                component, path=path,
            )
            SourceVoxelSpacing((2.0, 0.65, 0.65)).merge_into(component, path=path)
    volume = np.zeros((planes, 5, 7), dtype=np.uint16)
    volume[:, 1:3, 2:4] = 1
    for path, plane in zip(paths, volume):
        tifffile.imwrite(path, plane)
    provenance = SourceImageProvenancePlanes.from_components(paths=paths, component_metadata=components)

    @numpy_func(contract=ProcessingContract.PURE_3D)
    def synthetic_centres(image: np.ndarray) -> MeasurementTable:
        z, y, x = np.argwhere(image > 0).mean(axis=0)
        return MeasurementTable(
            name='synthetic_centres',
            rows=MeasurementSparseColumnarRows.from_rows(
                (dict(object_label=7, center_z=float(z), center_y=float(y), center_x=float(x)),),
                fields=(FieldSpec('object_label', int), FieldSpec('center_z', float),
                        FieldSpec('center_y', float), FieldSpec('center_x', float)),
            ),
            source_image_provenance_planes=provenance,
            subject=MeasurementSubject(MeasurementScope.OBJECT, 'synthetic', 'object_label'),
        )

    return synthetic_centres(volume), components, paths


@pytest.mark.parametrize('planes,origin', ((1, 0), (4, 0), (4, 10)))
@pytest.mark.parametrize('selected', (False, True))
@pytest.mark.parametrize('source_records', (False, True))
def test_original_point_writer_live_domain_anchor_and_reopen(tmp_path, planes, origin, selected, source_records):
    table, components, paths = point_fixture(tmp_path, planes, origin, source_records=source_records)
    feature = ObjectCoreMeasurementFeature
    options = PointROIOptions(
        z_feature=feature.CENTER_Z, y_feature=feature.CENTER_Y, x_feature=feature.CENTER_X,
        source='centres' if selected else None,
    )
    payload = {'centres': table} if selected else table
    spec = MaterializationSpec(CsvOptions(source=options.source), options)
    fm = FileManager({'disk': DiskStorageBackend()})
    outputs = materialization_outputs(
        spec, payload, str(tmp_path / 'centres'), fm,
        variable_components=(VariableComponents.Z_INDEX,),
    )
    point_output, = (output for output in outputs if isinstance(output, PointROIOutput))
    anchor = point_output.source_identity
    assert anchor.path == paths[0]
    assert dict(anchor.component_metadata) == components[0]
    assert point_output.metadata.source_image_provenance_planes.count == planes
    assert replace(point_output).source_identity == anchor
    assert not spec.emits_variable_component_planes(payload)
    identities = spec.stream_source_identities(payload)
    assert tuple(identity.path for identity in identities) == paths
    assert tuple(dict(identity.component_metadata) for identity in identities) == components

    archive = Path(materialize(
        MaterializationSpec(options), data=payload, path=str(tmp_path / 'saved'),
        filemanager=fm, backends=['disk'], backend_kwargs={},
    ))
    rois = load_rois_from_zip(archive)
    saved_metadata = ROIArchiveSourceMetadata.decode(rois)
    saved_domain = ROIFractionalZ.source_component_domain(rois, saved_metadata)
    assert tuple(dict(item) for item in saved_domain) == components
    assert saved_metadata.source_image_provenance_planes == point_output.metadata.source_image_provenance_planes
    if planes > 1:
        assert 'z_index' not in (saved_metadata.source_component_metadata or {})

    surface = StreamingViewerSurface(
        runtime_config=StreamingViewerRuntimeConfig(
            transport_endpoint=ViewerTransportEndpoint(host='127.0.0.1', port=6199, transport_mode=TransportMode.TCP),
            persistent=True, viewer_type=ViewerType.NAPARI,
        ),
        display_config=NapariStreamingConfig(enabled=True),
        source=ViewerStreamSourceIdentity(microscope_handler=SyntheticMicroscope(), plate_path=None),
    )
    items = ArtifactStreamSourceMetadataAuthority.metadata_items(
        materialization_spec=spec, data=payload, fallback_source_identity=None,
    )
    authority = StreamComponentMessageExtraAuthority.from_viewer_surface(surface, source_metadata_items=items)
    assert 'z_index' in authority.layout.component_order
    producer = StreamProducerIdentity.pipeline_output(
        output_kind='artifact', output_key='synthetic_centres', projection_key='synthetic_centres',
        step_name='Own engineering only', pipeline_position=0, artifact_kind='roi',
    )
    kwargs = ViewerStreamBackendCallKwargs(authority.viewer_backend_kwargs(
        producer=ViewerStreamProducer.from_identity(producer),
    )).to_filemanager_kwargs(point_output)
    request = kwargs['stream_request']
    streamed = request.source.metadata.component_metadata_for_item(index=0, file_path=point_output.path)
    assert int(streamed['z_index']) == origin
    domain = ViewerComponentValueDomainPayload.from_wire_mapping(
        authority.payload().to_wire_mapping()['component_value_domain'], context='own point source fixture',
    )
    item = NapariStreamLayerItem(
        data=NapariROIConverter.rois_to_shapes(rois), producer=producer,
        address=NapariStreamLayerAddress(components=anchor.component_metadata, path=str(archive), stream_layer_data_type=StreamingDataType.POINTS),
        image_metadata=saved_metadata, plane_component_domain=domain,
    )
    handler = NapariPointsLayerDisplayHandler()
    occupied = handler.geometric_component_values([item], authority.component_axis_semantics)
    assert occupied == {'z_index': list(range(origin, origin + (3 if planes == 4 else 1)))}
    with pytest.raises(ValueError, match='exceeds the declared Z domain'):
        handler.geometric_component_values(
            [replace(item, data=NapariROIConverter.rois_to_shapes([
                ROIFractionalZ(float(planes)).bind(rois[0]),
            ]))], authority.component_axis_semantics,
        )


def test_point_source_admission_reuses_original_typed_payload_contract():
    feature = ObjectCoreMeasurementFeature
    options = PointROIOptions(z_feature=feature.CENTER_Z, y_feature=feature.CENTER_Y, x_feature=feature.CENTER_X)
    with pytest.raises(TypeError, match='requires a MeasurementTable'):
        options.stream_source_identities(np.zeros((1, 5, 7)))


@pytest.mark.parametrize('field,value,error', (
    ('well', 'B01', 'vary outside Z'),
    ('site', 2, 'vary outside Z'),
    ('channel', 2, 'vary outside Z'),
    ('timepoint', 2, 'vary outside Z'),
    ('well', None, 'inconsistent components'),
    ('site', None, 'inconsistent components'),
    ('channel', None, 'inconsistent components'),
    ('timepoint', None, 'inconsistent components'),
    ('z_index', 0, 'consecutive and ordered'),
    ('z_index', 3, 'consecutive and ordered'),
    ('z_index', None, 'require z_index'),
    ('z_index', True, 'must be integers'),
    ('z_index', 1.5, 'must be integers'),
    ('z_index', '1.5', 'must be integers'),
    ('OpenHCSSourceVoxelSpacingZYX', '2,0.7,0.7', 'inconsistent calibration'),
    ('OpenHCSSourceVoxelSpacingUnit', 'relative', 'inconsistent calibration'),
))
def test_point_domain_preserves_real_coordinate_and_calibration_rejections(tmp_path, field, value, error):
    table, components, paths = point_fixture(tmp_path, 4, 0, source_records=True)
    invalid = tuple(dict(plane) for plane in components)
    if value is None:
        del invalid[1][field]
    else:
        invalid[1][field] = value
    metadata = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=paths, component_metadata=invalid,
        ),
    )
    from polystore.roi import ROI, PointShape
    rois = [ROIFractionalZ(1.5).bind(ROI(shapes=[PointShape(y=1.5, x=2.5)]))]
    with pytest.raises(ValueError, match=error):
        ROIFractionalZ.source_component_domain(rois, metadata)


@pytest.mark.parametrize('coordinate', (-0.5, 3.5))
def test_point_domain_preserves_fractional_z_bounds_with_literal_provenance(tmp_path, coordinate):
    table, components, paths = point_fixture(tmp_path, 4, 0, source_records=True)
    from polystore.roi import ROI, PointShape
    rois = [ROIFractionalZ(coordinate).bind(ROI(shapes=[PointShape(y=1.5, x=2.5)]))]
    with pytest.raises(ValueError, match='outside its source planes'):
        ROIFractionalZ.source_component_domain(
            rois, ImagePayloadMetadata(source_provenance=table.source_provenance),
        )
