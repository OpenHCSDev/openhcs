"""Tiny original PURE_3D producer -> typed Points writer -> live-domain control."""
from pathlib import Path
import argparse
from openhcs.serialization.json import to_jsonable
import json
import numpy as np
import tifffile

from openhcs.core.config import NapariStreamingConfig
from openhcs.core.memory import numpy as numpy_func
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.runtime_measurements import MeasurementTable, MeasurementSubject, MeasurementScope, ObjectCoreMeasurementFeature
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.processing.materialization import MaterializationSpec, PointROIOptions, materialize
from openhcs.core.steps.function_artifact_materialization import ArtifactStreamSourceMetadataAuthority
from openhcs.core.steps.stream_component_semantics import StreamComponentMessageExtraAuthority, StreamSourceComponentMetadataItems
from openhcs.core.streaming_config_factory import StreamingViewerSurface, StreamingViewerRuntimeConfig
from openhcs.core.streaming_config_declarations import ViewerType
from polystore.streaming.viewer_transport import ViewerStreamSourceIdentity
from polystore.filemanager import FileManager
from polystore.disk import DiskStorageBackend
from polystore.roi import load_rois_from_zip
from openhcs.core.roi_point_metadata import ROIFractionalZ
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from zmqruntime.viewer_protocol import ViewerTransportEndpoint
from zmqruntime.config import TransportMode

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True, help='New owned persistent synthetic directory; must not exist')
root = parser.parse_args().output
root.mkdir(exist_ok=False)
components = tuple({'well':'A01', 'site':1, 'channel':1, 'z_index':z, 'timepoint':1} for z in range(4))
paths = tuple(str(root / f'A01_s001_w1_z{z:03d}_t001.tif') for z in range(4))
volume = np.zeros((4,5,7), dtype=np.uint16)
volume[1:3,1:3,2:4] = 1
for z, path in enumerate(paths):
    tifffile.imwrite(path, volume[z])
provenance = SourceImageProvenancePlanes.from_components(paths=paths, component_metadata=components)
metadata = ImagePayloadMetadata(source_image_provenance_planes=provenance, source_component_metadata={k:v for k,v in components[0].items() if k!='z_index'}, source_voxel_spacing=SourceVoxelSpacing((2.0,0.65,0.65)),plane_axis=RuntimePlaneAxis.SOURCE_BINDING)

@numpy_func(contract=ProcessingContract.PURE_3D)
def synthetic_centres(image: np.ndarray) -> MeasurementTable:
    assert image.shape == (4,5,7)
    z,y,x = np.argwhere(image > 0).mean(axis=0)
    return MeasurementTable(name='synthetic_centres',
        rows=MeasurementSparseColumnarRows.from_rows(({'object_label':7,'center_z':float(z),'center_y':float(y),'center_x':float(x)},),
            fields=(FieldSpec('object_label',int),FieldSpec('center_z',float),FieldSpec('center_y',float),FieldSpec('center_x',float))),
        source_image_provenance_planes=provenance, source_component_metadata=metadata.source_component_metadata,
        subject=MeasurementSubject(MeasurementScope.OBJECT,'synthetic','object_label'))

table = synthetic_centres(metadata.attach_to(volume))
spec = MaterializationSpec(PointROIOptions(z_feature=ObjectCoreMeasurementFeature.CENTER_Z,y_feature=ObjectCoreMeasurementFeature.CENTER_Y,x_feature=ObjectCoreMeasurementFeature.CENTER_X))
archive = materialize(spec,data=table,path=str(root/'centres'),filemanager=FileManager({'disk':DiskStorageBackend()}),backends=['disk'],backend_kwargs={})
items = ArtifactStreamSourceMetadataAuthority.metadata_items(materialization_spec=spec,data=table,fallback_source_identity=None)
surface = StreamingViewerSurface(
    runtime_config=StreamingViewerRuntimeConfig(transport_endpoint=ViewerTransportEndpoint(host='127.0.0.1',port=6199,transport_mode=TransportMode.TCP),persistent=True,viewer_type=ViewerType.NAPARI),
    display_config=NapariStreamingConfig(enabled=True), source=ViewerStreamSourceIdentity(microscope_handler=None,plate_path=None))
authority = StreamComponentMessageExtraAuthority.from_viewer_surface(surface,source_metadata_items=items)
saved_rois = load_rois_from_zip(Path(archive))
saved_metadata = ROIArchiveSourceMetadata.decode(saved_rois)
saved_domain = ROIFractionalZ.source_component_domain(saved_rois, saved_metadata)
reopened = StreamComponentMessageExtraAuthority.from_viewer_surface(surface, source_metadata_items=StreamSourceComponentMetadataItems.from_values(saved_domain))
result = dict(saved_domain=saved_domain, archive_scalar_metadata=saved_metadata.source_component_metadata, archive=archive,shape=volume.shape,rows=tuple(table.iter_row_mappings()),source_component_order=authority.layout.component_order,declared_domain=authority.payload().to_wire_mapping(), scientific_data_opened=False,runtime_started=False)
print(json.dumps(to_jsonable(result),sort_keys=True))
assert 'z_index' not in authority.layout.component_order, 'Expected original live-source defect no longer reproduces; update this engineering control'
metadata = saved_metadata
rois = saved_rois
live = authority
archive = Path(archive)

from polystore.roi_converters import NapariROIConverter
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming_constants import StreamingDataType
from openhcs.runtime.napari_streaming_handlers import NapariStreamLayerItem, NapariStreamLayerAddress
from openhcs.runtime.viewer_component_system import ViewerComponentValueDomainPayload
from openhcs.runtime.napari_viewer_server import NapariPointsLayerDisplayHandler

anchor = metadata.source_provenance.for_source_plane(0).scalar_source_identity
domain = ViewerComponentValueDomainPayload.from_wire_mapping(reopened.payload().to_wire_mapping()['component_value_domain'],context='own synthetic source-bearing points')
item = NapariStreamLayerItem(
    data=NapariROIConverter.rois_to_shapes(rois),
    producer=StreamProducerIdentity.pipeline_output(output_kind='artifact',output_key='synthetic_centres',projection_key='synthetic_centres',step_name='Own engineering only',pipeline_position=0,artifact_kind='roi'),
    address=NapariStreamLayerAddress(components=anchor.component_metadata,path=str(archive),stream_layer_data_type=StreamingDataType.POINTS),
    image_metadata=metadata,plane_component_domain=domain)
handler = NapariPointsLayerDisplayHandler()
results = {}
for name, fallback in [('none',None),('common',metadata.source_provenance.scalar_source_identity),('first_plane',anchor)]:
    items = ArtifactStreamSourceMetadataAuthority.metadata_items(materialization_spec=spec,data=table,fallback_source_identity=fallback)
    authority = StreamComponentMessageExtraAuthority.from_viewer_surface(surface,source_metadata_items=items)
    try:
        geometry = handler.geometric_component_values([item],authority.component_axis_semantics)
    except ValueError as error:
        results[name] = dict(order=authority.layout.component_order,error=str(error))
    else:
        raise AssertionError(f'Incomplete live domain unexpectedly accepted: {name}: {geometry!r}')
positive = handler.geometric_component_values([item],reopened.component_axis_semantics)
assert results['none']['error'] == 'Fractional-Z point ROI requires a projected z_index axis.'
assert results['common']['error'] == results['none']['error']
assert 'exceeds the declared Z domain' in results['first_plane']['error']
assert positive == {'z_index':[0,1,2]}
print(json.dumps(dict(negative=results,original_domain_positive=positive,viewer_started=False,connected=False),sort_keys=True))
