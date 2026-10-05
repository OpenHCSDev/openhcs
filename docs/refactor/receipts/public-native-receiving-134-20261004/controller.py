"""One bounded synthetic receiving journey through actual metadata/writer and public MCP."""
from __future__ import annotations
from dataclasses import replace
import asyncio, hashlib, json, os, secrets, socket, subprocess, sys, time, traceback
from pathlib import Path
SOURCE=Path('/var/tmp/openhcs-resolved-pipeline-owner-20261004')
OUT=Path('/home/ts/.local/state/openhcs-maintenance/20261004/receiving-134-native')
PYTHON=Path('/home/ts/code/projects/openhcs/.venv/bin/python')
PORT=6609; DISPLAY=':119'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def environment():
 e=dict(os.environ)
 for k in tuple(e):
  if k.startswith('OPENHCS_PROFILE_') or k.startswith('OPENHCS_DIAGNOSTIC_'): del e[k]
 e.update(PYTHONPATH=str(SOURCE),PYTHONDONTWRITEBYTECODE='1',OPENHCS_CPU_ONLY='true',OPENHCS_HEADLESS='false',OPENHCS_SUBPROCESS_NO_GPU='1',POLYSTORE_SUBPROCESS_NO_GPU='1',CUDA_VISIBLE_DEVICES='',QT_QPA_PLATFORM='xcb',DISPLAY=DISPLAY,XAUTHORITY=str(OUT/'owned.xauthority'),LIBGL_ALWAYS_SOFTWARE='1',QT_OPENGL='software',OPENHCS_AGENT_READ_ROOTS=os.pathsep.join((str(OUT),str(SOURCE))),OPENHCS_AGENT_WRITE_ROOTS=str(OUT),POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD='false',OPENHCS_UI_CONFIG_CACHE_FILE=str(OUT/'owned/ui-config.config'))
 e.pop('WAYLAND_DISPLAY',None)
 for key,sub in [('XDG_DATA_HOME','data'),('XDG_CONFIG_HOME','config'),('XDG_CACHE_HOME','cache'),('XDG_STATE_HOME','state'),('XDG_RUNTIME_DIR','runtime'),('MPLCONFIGDIR','matplotlib'),('NUMBA_CACHE_DIR','numba')]: e[key]=str(OUT/'owned'/sub)
 for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','NUMBA_NUM_THREADS','BLIS_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):e[key]='1'
 return e
if '--worker' not in sys.argv:
 for sub in ('data','config','cache','state','runtime','matplotlib','numba'): (OUT/'owned'/sub).mkdir(parents=True,exist_ok=True)
 (OUT/'owned/runtime').chmod(0o700)
 assert not (OUT/'journey-live12.json').exists(), 'Never overwrite a receiving attempt'
 with (OUT/'controller-live12.log').open('x') as log:
  r=subprocess.run(['/usr/bin/systemd-run','--user','--scope','--quiet','-p','MemoryMax=1800M','-p','MemorySwapMax=0','-p','TasksMax=256','/usr/bin/env',*[f'{k}={v}' for k,v in environment().items()],'/usr/bin/taskset','-c','3',str(PYTHON),'-B',__file__,'--worker'],env=dict(os.environ),cwd='/var/tmp',stdout=log,stderr=subprocess.STDOUT,timeout=360)
 print(json.dumps({'returncode':r.returncode,'receipt':str(OUT/'journey-live12.json')})); sys.exit(r.returncode)
sys.path.insert(0,str(SOURCE))
import openhcs
assert Path(openhcs.__file__).resolve()==SOURCE/'openhcs/__init__.py'
import numpy as np, tifffile
import importlib.metadata as package_metadata
receipt_dependencies={name:package_metadata.version(name) for name in ('python-introspect','polystore','zmqruntime','napari','numpy','PyQt6')}
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.virtual_workspace import SourcePixelRef
from polystore.roi import load_rois_from_zip
from openhcs.constants import AllComponents
from openhcs.core.plate_file_inventory import PlateFileKind
from openhcs.core.artifacts import ArtifactOutputPlan,ArtifactSpec,ObjectLabelsArtifactType,SpatialGraphArtifactType,ObjectArtifactMemberSubjectRelation
from openhcs.core.source_projection import OpenHCSPlaneAddress,SourcePlaneProjection,SourceProjectionMetadataSerializer
from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter,VirtualWorkspaceSourceProjectionEntries,METADATA_CONFIG
from openhcs.microscopes.imagexpress import ImageXpressFilenameParser,ImageXpressHandler
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.runtime_spatial_graph import SpatialGraph,SpatialGraphNode,SpatialGraphEdge
from openhcs.core.steps.function_runtime import FunctionOutputContextStrategy
from openhcs.processing.materialization import MaterializationSpec,SpatialGraphROIOptions,materialize
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.plate import PlateFileStreamRequest
from openhcs.agent.dto.common import AgentResourceRef
from openhcs.agent.dto.viewer import ViewerWindowStateRequest,ViewerWindowSnapshotRequest,ViewerWindowCloseRequest,ViewerWindowLayerIsolationRequest,ViewerWindowImageSampleRequest,ViewerWindowRoiSummaryRequest,ViewerWindowPayloadRequest,ViewerWindowViewportRequest
from openhcs.mcp.dev_client_core import McpDevServerSpec,McpDevStdioSession,McpDevToolResult
from openhcs.serialization.json import to_jsonable
from zmqruntime.config import TransportMode
from zmqruntime.transport import TransportEndpoint
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
conn=ExecutionConnectionSpec(host='127.0.0.1',port=PORT,transport_mode=TransportMode.TCP,persistent=True)
receipt={'accepted':False,'scope':'Synthetic native receiving only; no biological processing or native CP rerun','source_head':subprocess.check_output(['git','-C',str(SOURCE),'rev-parse','HEAD'],text=True).strip(),'source':str(SOURCE),'controller_sha256':sha(__file__),'calls':[],'failure':None,'children':[],'installed_dependencies':receipt_dependencies}
def save(): (OUT/'journey-live12.json').write_text(json.dumps(receipt,indent=2)+'\n')
def prepare_fixture():
 raw=OUT/'raw_plate'; labels=OUT/'labels_plate'
 if raw.exists():
  for root in (raw,labels):
   doc=json.loads(METADATA_CONFIG.metadata_path(root).read_text())
   (OUT/(root.name+'-metadata-invalid-axis.json')).write_text(json.dumps(doc,indent=2)+'\n')
  doc=json.loads(METADATA_CONFIG.metadata_path(raw).read_text())
  owner=VirtualWorkspaceSourceProjectionEntries.from_subdirectory(doc['subdirectories']['images'])
  scalar=VirtualWorkspaceSourceProjectionEntries({path:replace(projection,image_metadata=replace(projection.image_metadata,plane_axis=None)) for path,projection in owner.entries.items()})
  AtomicMetadataWriter().merge_source_projection_metadata(METADATA_CONFIG.metadata_path(raw),'images',scalar)
  paths=tuple(raw/'images'/f'A01_s001_w{ch}_z001_t001.tif' for ch in (2,1))
  components=tuple(dict(scalar.entries[str(path)].source_metadata) for path in paths)
  spacing=SourceVoxelSpacing((1.3556,1.3556))
  metadata=ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,source_image_provenance_planes=SourceImageProvenancePlanes.from_components(paths=tuple(map(str,paths)),component_metadata=components),source_image_names=('raw_2','raw_1'),source_spatial_domain=SourceSpatialDomain((0,0),(32,32)),source_voxel_spacing=spacing)
  target=labels/'stacked_labels'/'A01_s001_w2_z001_t001_Labels.tif';target.parent.mkdir(exist_ok=True)
  pixels=np.stack([tifffile.imread(labels/'images'/path.name) for path in paths])
  if target.exists():np.testing.assert_array_equal(tifffile.imread(target),pixels)
  else:tifffile.imwrite(target,pixels,photometric='minisblack',metadata={'axes':'ZYX'})
  projection=SourcePlaneProjection(address=OpenHCSPlaneAddress.from_values('A01',1,2,1,1),ref=SourcePixelRef('disk',str(target)),source_metadata=components[0],image_metadata=metadata)
  AtomicMetadataWriter().merge_subdirectory_metadata(METADATA_CONFIG.metadata_path(labels),{'images':{'main':False}})
  AtomicMetadataWriter().publish_source_projection_metadata(METADATA_CONFIG.metadata_path(labels),'stacked_labels',VirtualWorkspaceSourceProjectionEntries.from_projection_paths(((projection,str(target)),)),serializer=SourceProjectionMetadataSerializer(ImageXpressFilenameParser()),saved_image_paths=(str(target),),microscope_handler_name=ImageXpressHandler._microscope_type,source_filename_parser_name='ImageXpressFilenameParser',component_labels={},backend='disk',is_main=True,results_dir=str(labels/'graph_results'))
  graph=labels/'graph_results'/'A01_s001_w2_z001_t001_graph.graph.roi.zip'
  restored=load_rois_from_zip(graph); graph_metadata=ROIArchiveSourceMetadata.decode(restored)
  assert graph_metadata.source_voxel_spacing==spacing
  expected={str(path):tifffile.imread(path).tolist() for path in (*paths,target)}
  receipt['fixture']={'raw':str(raw),'labels':str(labels),'label_paths':[str(target)],'graph':str(graph),'metadata':to_jsonable(graph_metadata),'label_metadata':to_jsonable(metadata),'roi_features':[to_jsonable(r.metadata) for r in restored],'files':{str(p):sha(p) for root in (raw,labels) for p in root.rglob('*') if p.is_file()},'expected_pixels':expected,'retained_failed_receipts':[str(OUT/f'journey-{name}.json') for name in ('live','live2','live3','live4','live5')]};save()
  assert pixels.shape==(2,32,32) and metadata.source_image_provenance_planes.count==2
  return raw,labels,graph

 for root in (raw,labels):(root/'images').mkdir(parents=True)
 spacing=SourceVoxelSpacing((1.3556,1.3556)); domain=SourceSpatialDomain((0,0),(32,32)); rows=[]
 for ch in (2,1):
  path=raw/'images'/f'A01_s001_w{ch}_z001_t001.tif'; pixels=(np.arange(1024,dtype=np.uint16).reshape(32,32)+ch*100)
  tifffile.imwrite(path,pixels,photometric='minisblack',metadata={'axes':'YX'}); rows.append((ch,path,pixels))
 entries={raw:[],labels:[]}; expected={}
 for ch,path,pixels in rows:
  components={'well':'A01','site':'1','channel':str(ch),'z_index':'1','timepoint':'1'}; spacing.merge_into(components,path=str(path))
  metadata=ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,source_image_provenance_planes=SourceImageProvenancePlanes.from_components(paths=(str(path),),component_metadata=(components,)),source_image_names=(f'raw_{ch}',),source_spatial_domain=domain,source_voxel_spacing=spacing)
  for root in (raw,labels):
   target=root/'images'/path.name
   if root==labels:
    label=np.zeros((32,32),dtype=np.uint16);label[3:12,4:14]=7;label[17:25,20:28]=11
    label*=ch; tifffile.imwrite(target,label,photometric='minisblack',metadata={'axes':'YX'})
   expected[str(target)]=tifffile.imread(target).tolist()
   entries[root].append((SourcePlaneProjection(address=OpenHCSPlaneAddress.from_values('A01',1,ch,1,1),ref=SourcePixelRef('disk',str(target)),source_metadata=components,image_metadata=metadata),str(target)))
 for root in (raw,labels):
  AtomicMetadataWriter().publish_source_projection_metadata(METADATA_CONFIG.metadata_path(root),'images',VirtualWorkspaceSourceProjectionEntries.from_projection_paths(entries[root]),serializer=SourceProjectionMetadataSerializer(ImageXpressFilenameParser()),saved_image_paths=tuple(p for _,p in entries[root]),microscope_handler_name='ImageXpress',source_filename_parser_name='ImageXpressFilenameParser',component_labels={},backend='disk',is_main=True,results_dir=str(labels/'graph_results') if root==labels else None)
 nodes=tuple(SpatialGraphNode(i+1,xy) for i,xy in enumerate(((2.25,3.5),(5.25,9.5),(7.25,12.5))))
 edges=tuple(SpatialGraphEdge.from_features(edge_id=i+1,source=nodes[i],target=nodes[i+1],coordinates=np.asarray((nodes[i].coordinates,nodes[i+1].coordinates)),features={'neuron_label':7,'branch_distance_um':8.5}) for i in range(2))
 graph=SpatialGraph(name='declared_graph',nodes=nodes,edges=edges,coordinate_spacing=spacing.values_zyx,source_plane_index=0)
 plan=ArtifactOutputPlan(name=graph.name,path=str(labels/'graph.pkl'),artifact_type=SpatialGraphArtifactType,relations=(ObjectArtifactMemberSubjectRelation(source=ArtifactSpec.output('neurons',ObjectLabelsArtifactType).ref(),member_id_field='neuron_label'),),producer_step_index=4,producer_step_scope_id='synthetic-receiving-134')
 source_metadata=ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,source_image_provenance_planes=SourceImageProvenancePlanes.from_components(paths=tuple(str(path) for _,path,_ in rows),component_metadata=tuple(dict(p.source_metadata) for p,_ in entries[raw])),source_image_names=('raw_2','raw_1'),source_spatial_domain=domain,source_voxel_spacing=spacing)
 graph=FunctionOutputContextStrategy.for_output_plan(plan).contextualize(source_metadata.payload_with(np.stack([pixels for _,_,pixels in rows])),graph,plan,None)
 graph_path=labels/'graph_results'/'A01_s001_w2_z001_t001_graph.roi.zip';graph_path.parent.mkdir()
 materialize(MaterializationSpec(SpatialGraphROIOptions()),data=graph,path=str(graph_path),filemanager=FileManager({'disk':DiskStorageBackend()}),backends=['disk'],backend_kwargs={},output_plan=plan)
 restored=load_rois_from_zip(graph_path); decoded=ROIArchiveSourceMetadata.decode(restored)
 assert decoded.source_provenance==source_metadata.source_provenance.for_source_plane(0)
 receipt['fixture']={'raw':str(raw),'labels':str(labels),'graph':str(graph_path),'spacing':to_jsonable(spacing),'metadata':to_jsonable(decoded),'roi_features':[to_jsonable(r.metadata) for r in restored],'files':{str(p):sha(p) for root in (raw,labels) for p in root.rglob('*') if p.is_file()},'expected_pixels':expected};save()
 return raw,labels,graph_path
async def call(session,name,args,*,allow_error=False):
 raw=await session.call_tool(name,args,timeout_seconds=45); decoded=McpDevToolResult.from_payload(name,raw)
 payload=to_jsonable(decoded.first_decoded_payload()); receipt['calls'].append({'tool':name,'arguments':args,'response':raw,'payload':payload});save()
 if not allow_error:assert not decoded.has_errors(),to_jsonable(decoded.diagnostic_errors())
 return payload
async def journey():
 children=[]; xserver=None; active=False
 try:
  for displaypath in (Path('/tmp/.X119-lock'),Path('/tmp/.X11-unix/X119')):assert not displaypath.exists(), f'Foreign display reservation {displaypath}'
  endpoint=TransportEndpoint('127.0.0.1',PORT,TransportMode.TCP)
  ports=sorted(endpoint.port_pair(OPENHCS_ZMQ_CONFIG).ports)
  for port in ports:
   lock=TransportMode.TCP.declaration.startup_lock_path(port,OPENHCS_ZMQ_CONFIG);assert not lock.exists(),str(lock)
   with socket.socket() as sock:assert sock.connect_ex(('127.0.0.1',port))!=0,port
  receipt['owned_ports']=ports
  raw,labels,graph=prepare_fixture()
  auth=OUT/'owned.xauthority';auth.touch(mode=0o600)
  subprocess.run(['xauth','-f',str(auth),'add',DISPLAY,'.',secrets.token_hex(16)],check=True,stdout=subprocess.DEVNULL)
  with (OUT/'xserver-live12.log').open('x') as xlog:
   xserver=subprocess.Popen([str(OUT/'private-xserver/usr/bin/Xvfb'),DISPLAY,'-screen','0','1280x960x24','-nolisten','tcp','-auth',str(auth)],stdout=xlog,stderr=subprocess.STDOUT)
  receipt['xserver_pid']=xserver.pid;save()
  for _ in range(50):
   if Path('/tmp/.X11-unix/X119').exists():break
   assert xserver.poll() is None;await asyncio.sleep(.1)
  assert Path('/tmp/.X11-unix/X119').exists()
  with (OUT/'mcp-live12.log').open('x') as log:
   async with McpDevStdioSession(McpDevServerSpec(str(PYTHON)),log) as session:
    children.append(session.require_process());await session.initialize(timeout_seconds=90);await session.list_tools(timeout_seconds=90)
    health=await call(session,'openhcs_health_check',{});assert Path(health['server_source_path']).resolve()==SOURCE/'openhcs/mcp/server.py'
    for plate in (raw,labels):
     inventory=await call(session,'openhcs_query_plate_files',{'plate_path':str(plate),'kind':'image','limit':10});assert inventory['total_count']==(2 if plate==raw else 3) and not inventory['warnings'],inventory
    label_paths=receipt['fixture']['label_paths']
    prior=json.loads((OUT/'journey-live8.json').read_text())
    assert prior['source_head']==receipt['source_head'] and prior['installed_dependencies']==receipt['installed_dependencies']
    state=next(row['payload'] for row in prior['calls'] if row['tool']=='openhcs_get_viewer_window_state')
    receipt_path=OUT/'label-source-receipt.json';assert json.loads(receipt_path.read_text())==state
    from openhcs.agent.dto.viewer import ViewerWindowStateResult
    typed=ViewerWindowStateResult.from_mapping(state)
    for path in label_paths:
     record,_=typed.image_payload_binding_for(path);assert record.summary.voxel_spacing==SourceVoxelSpacing((1.3556,1.3556))
    receipt['initial_native_qualification']={'receipt':str(OUT/'journey-live8.json'),'sha256':sha(OUT/'journey-live8.json'),'native_state':str(receipt_path),'state_sha256':sha(receipt_path)};save()
    ref=AgentResourceRef(uri=receipt_path.as_uri(),title='Actual calibrated native label state',path=str(receipt_path),size_bytes=receipt_path.stat().st_size,sha256=sha(receipt_path))
    active=True
    await call(session,'openhcs_stream_plate_files_to_viewer',PlateFileStreamRequest(plate_path=str(labels),result_directory=str(labels/'stacked_labels'),file_paths=tuple(label_paths),kind=PlateFileKind.RESULT,limit=2,connection=conn,fresh_viewer=True,source_receipt=ref).as_tool_arguments())
    await call(session,'openhcs_stream_plate_files_to_viewer',PlateFileStreamRequest(plate_path=str(raw),limit=2,connection=conn).as_tool_arguments())
    inventory=await call(session,'openhcs_query_plate_files',{'plate_path':str(labels),'result_directory':str(graph.parent),'kind':'result','limit':10})
    await call(session,'openhcs_stream_plate_files_to_viewer',PlateFileStreamRequest(plate_path=str(labels),context_plate_path=str(raw),result_directory=str(graph.parent),file_paths=(str(graph),),kind=PlateFileKind.RESULT,limit=1,connection=conn).as_tool_arguments())
    state=await call(session,'openhcs_get_viewer_window_state',ViewerWindowStateRequest(connection=conn).as_tool_arguments());(OUT/'combined-state.json').write_text(json.dumps(state,indent=2)+'\n')
    typed=ViewerWindowStateResult.from_mapping(state)
    route_for={summary.path:layer.route_key for layer in typed.layers for summary in layer.payload_summaries}
    raw_routes={route_for[path] for path in receipt['fixture']['expected_pixels'] if '/raw_plate/' in path}
    label_routes={route_for[path] for path in label_paths}; graph_route=route_for[str(graph)]
    assert raw_routes.isdisjoint(label_routes),(raw_routes,label_routes)
    seen=set()
    payloads=await call(session,'openhcs_get_viewer_window_payloads',ViewerWindowPayloadRequest.from_fields(connection=conn,include_array_values=True,max_array_elements=4096,include_shape_payloads=True,max_shape_payloads=20).as_tool_arguments())
    for layer in payloads['layers']:
     for record in layer['payloads']:
      if record['data_type']!='image':continue
      path=record['path'];assert path in receipt['fixture']['expected_pixels'],record
      expected=np.asarray(receipt['fixture']['expected_pixels'][path])
      plane=record['aggregate_axis_indices'][0] if expected.ndim==3 else None
      selected=expected[plane] if plane is not None else expected
      np.testing.assert_array_equal(np.asarray(record['array_values']).reshape(selected.shape),selected);seen.add((path,plane))
    wanted={(path,plane) for path,values in receipt['fixture']['expected_pixels'].items() for plane in (range(len(values)) if np.asarray(values).ndim==3 else (None,))}
    assert seen==wanted,seen
    roi=await call(session,'openhcs_summarize_viewer_window_rois',ViewerWindowRoiSummaryRequest(connection=conn,route_key=graph_route,max_examples=10).as_tool_arguments())
    assert roi['observed'] and roi['total_roi_count']==len(receipt['fixture']['roi_features']) and roi['roi_count_exact'],roi
    for payload in roi['payloads']:
     assert payload['components']['channel'] in ('2',2),payload
     assert payload['out_of_source_bounds_count']==0,payload
    await call(session,'openhcs_get_viewer_window_payloads',ViewerWindowPayloadRequest.from_fields(connection=conn,route_key=graph_route,include_shape_payloads=True,max_shape_payloads=20).as_tool_arguments())
    captures={}; matched=[]; viewport=typed.native_viewport
    for name,routes in [('raw',raw_routes),('result',label_routes|{graph_route}),('combined',raw_routes|label_routes|{graph_route})]:
     await call(session,'openhcs_isolate_viewer_window_layers',ViewerWindowLayerIsolationRequest.from_fields(connection=conn,visible_route_keys=sorted(routes),selected_route_key=next(iter(sorted(label_routes if label_routes.issubset(routes) else raw_routes))),axis_indices={'channel':1}).as_tool_arguments())
     await call(session,'openhcs_set_viewer_viewport',ViewerWindowViewportRequest.from_fields(connection=conn,presentation=viewport).as_tool_arguments())
     observed=await call(session,'openhcs_get_viewer_window_state',ViewerWindowStateRequest(connection=conn).as_tool_arguments());matched.append(observed['native_viewport'])
     assert {l['route_key'] for l in observed['layers'] if l['visible']}==routes,observed
     captures[name]=await call(session,'openhcs_viewer_snapshot_window',ViewerWindowSnapshotRequest.from_fields(connection=conn,output_dir_path=str(OUT/'captures-live12'/name)).as_tool_arguments())
     assert captures[name]['captured'],captures[name]
    assert matched[0]==matched[1]==matched[2],matched
    receipt['captures']=captures;receipt['complete_native_pixel_paths']=sorted(seen);receipt['accepted']=True
    await call(session,'openhcs_close_viewer_window',ViewerWindowCloseRequest(connection=conn,confirmed=True).as_tool_arguments());active=False
 except BaseException as error:
  receipt['failure']={'type':type(error).__name__,'message':str(error),'traceback':traceback.format_exc()};save();raise
 finally:
  if active:
   with (OUT/'cleanup-mcp-live12.log').open('x') as log:
    async with McpDevStdioSession(McpDevServerSpec(str(PYTHON)),log) as session:
     children.append(session.require_process());await session.initialize(timeout_seconds=90)
     receipt['cleanup']=await call(session,'openhcs_close_viewer_window',ViewerWindowCloseRequest(connection=conn,confirmed=True).as_tool_arguments(),allow_error=True)
  if xserver is not None:
   xserver.terminate()
   try:xserver.wait(timeout=5)
   except subprocess.TimeoutExpired:xserver.kill();xserver.wait(timeout=5)
   receipt['xserver_returncode']=xserver.returncode
  receipt['dependencies_unchanged']=receipt_dependencies=={name:package_metadata.version(name) for name in receipt_dependencies}
  receipt['mcp_children']=[{'pid':p.pid,'returncode':p.returncode} for p in children];save()
asyncio.run(journey())
