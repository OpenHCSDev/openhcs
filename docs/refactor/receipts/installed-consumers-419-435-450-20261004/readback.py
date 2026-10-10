"""Read-only fresh public SDK acceptance; original failed receipt is immutable."""
from __future__ import annotations
import ast, asyncio, hashlib, importlib.util, json, os, subprocess, sys, time, traceback
from pathlib import Path
from csv import DictReader
CONTROLLER = Path('/var/tmp/run_public_installed_consumers_419_435_450_v7_20261004.py')
EVIDENCE = Path('/home/ts/.local/state/openhcs-maintenance/20261004/installed-consumer-419-435-450-v7-readback-v2')
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('frozen_v7_controller',CONTROLLER)
original=importlib.util.module_from_spec(spec); spec.loader.exec_module(original)
freeze=json.loads((original.OUTPUT/'source-freeze.json').read_text())
original.validate(freeze)
journey=json.loads((original.OUTPUT/'journey.json').read_text())
assert not journey['accepted'] and journey['failure']['type']=='AssertionError'
assert journey['owned_runtime_terminal'] and journey['mcp_children_terminal']
for key in ('compile','execution'):
    state=journey['installed_cases']['saved-label-geometry-distance-resize'][key]
    assert state['status']=='complete' and not state['errors'], state
if '--worker' not in sys.argv:
    EVIDENCE.mkdir(exist_ok=False)
    with (EVIDENCE/'controller.log').open('x') as output:
        result=subprocess.run(['/usr/bin/taskset','-c','3',str(original.PYTHON),'-B',__file__,'--worker'],cwd='/var/tmp',env=original.environment(),stdout=output,stderr=subprocess.STDOUT,timeout=300)
    print(json.dumps({'returncode':result.returncode,'receipt':str(EVIDENCE/'receipt.json')}))
    sys.exit(result.returncode)
sys.path.insert(0,str(original.SOURCE))
import openhcs
assert Path(openhcs.__file__).resolve()==original.SOURCE/'openhcs/__init__.py'
import numpy as np, tifffile
from scipy.ndimage import distance_transform_edt
from openhcs.mcp.dev_client_core import McpDevServerSpec, McpDevStdioSession, McpDevToolResult
from python_introspect import to_jsonable
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG
from benchmark.cellprofiler_reference_exports import CellProfilerReferenceExportArtifact, CellProfilerReferenceArtifactComparison
roots=(original.PRIOR/'outputs',original.IPO_PRIOR/'outputs',original.OUTPUT/'outputs')
def inventory(): return {str(p):sha(p) for root in roots for p in sorted(root.rglob('*')) if p.is_file()}
immutable_paths=(CONTROLLER, original.OUTPUT/'journey.json',original.OUTPUT/'source-freeze.json',original.PRIOR/'journey.json',original.IPO_PRIOR/'journey.json',Path('/home/ts/.local/state/openhcs-maintenance/20261004/installed-consumer-419-435-450-v7-readback/receipt.json'))
immutable={str(p):sha(p) for p in immutable_paths}
receipt=dict(journey)
receipt.update(accepted=False,scope='Read-only fresh MCP SDK acceptance of immutable original435, public IPO and saved Shape/DISTANCE/prepared Resize consumer outputs. No runtime startup or processing replay. Original v7 failed checker receipt retained.',failure=None,calls=[],readers=[],original_failure=journey['failure'],original_journey=str(original.OUTPUT/'journey.json'),immutable_before=immutable,output_files_before=inventory(),helper_sha256=sha(__file__),calibration_correction={'reason':'ResizeGeometry.resize_payload uses ImagePayloadMetadata.with_spatial_resize, which changes only local SourceSpatialDomain and border/mask facts. Original source calibration remains unchanged; no calibration rescale is part of the existing contract.','source_files':{rel:sha(original.SOURCE/rel) for rel in ('openhcs/core/runtime_image_values.py','openhcs/core/source_spatial_domain.py','openhcs/processing/backends/cellprofiler/image_geometry.py','tests/unit/test_cellprofiler_resize_hotpath.py')}})
def save(): (EVIDENCE/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
allowed={'openhcs_health_check','openhcs_inspect_plate_path','openhcs_query_plate_files','openhcs_sample_plate_image'}
async def call(session,name,arguments):
    assert name in allowed
    raw=await session.call_tool(name,arguments,timeout_seconds=30)
    decoded=McpDevToolResult.from_payload(name,raw)
    assert not decoded.has_errors(),to_jsonable(decoded.diagnostic_errors())
    result=to_jsonable(decoded.first_decoded_payload()); assert isinstance(result,dict)
    receipt['calls'].append({'tool':name,'arguments':arguments,'response':raw}); save()
    return result
# Reuse the exact original complete-pixel/public-inventory readers. The only
# correction is the rejected checker assumption about source calibration.
tree=ast.parse(CONTROLLER.read_text())
worker=next(node for node in tree.body if isinstance(node,ast.AsyncFunctionDef) and node.name=='worker')
namespace=globals()|{'OUTPUT':original.OUTPUT,'PRIOR':original.PRIOR,'ALIASES':original.ALIASES}
for name in ('inspect_outputs','inspect_saved_case'):
    node=next(node for node in worker.body if isinstance(node,ast.AsyncFunctionDef) and node.name==name)
    source=ast.unparse(node)
    if name=='inspect_saved_case':
        old="wanted = 1.3556 if alias == 'SavedDistance' else 0.6778"
        assert source.count(old)==1
        source=source.replace(old,'wanted = 1.3556')
        old_cardinality = "assert len(records) == 1, (alias, records, inventory)\n        record = records[0]"
        assert source.count(old_cardinality)==1
        source=source.replace(old_cardinality, """document = json.loads(METADATA_CONFIG.metadata_path(root).read_text())
        projection_rows = [row for directory in document['subdirectories'].values() for row in directory.get('source_projection', []) if '_' + alias in Path(row['virtual_path']).stem]
        assert len(records) == len(projection_rows), (alias, records, projection_rows)
        primary_paths = {row['virtual_path'] for row in projection_rows if row['projection_role'] == 'primary_plane'}
        primary_records = [record for record in records if record['virtual_path'] in primary_paths]
        assert len(primary_records) == 1, (alias, records, projection_rows)
        for occurrence in records:
            physical = tifffile.imread(Path(occurrence['source_path']))
            np.testing.assert_allclose(physical, pixels, rtol=1e-6, atol=1e-6)
            assert physical.shape == pixels.shape and physical.dtype == np.float32
            occurrence_sample = await call(session, 'openhcs_sample_plate_image', {'plate_path': str(root), 'image_path': occurrence['virtual_path'], 'microscope_type': 'auto', 'y': 0, 'x': 0, 'height': 2, 'width': 2, 'max_array_elements': 4, 'include_array_values': True})
            assert tuple(occurrence_sample['shape']) == pixels.shape and occurrence_sample['sample_included']
            np.testing.assert_array_equal(np.asarray(occurrence_sample['sample_values'], dtype=np.float32).reshape(2,2), physical[:2,:2])
        record = primary_records[0]""")
    exec(compile(source,str(CONTROLLER)+'::'+name,'exec'),namespace)
async def readback():
    children=[]
    try:
        with (EVIDENCE/'fresh-reader-stderr.log').open('x') as stderr:
            async with McpDevStdioSession(McpDevServerSpec(str(original.PYTHON)),stderr) as session:
                process=session.require_process(); children.append(process)
                receipt['readers'].append({'pid':process.pid,'source':str(original.SOURCE)})
                await session.initialize(timeout_seconds=180)
                await session.list_tools(timeout_seconds=180)
                health=await call(session,'openhcs_health_check',{})
                assert Path(health['server_source_path']).resolve()==original.SOURCE/'openhcs/mcp/server.py'
                assert not health['errors'] and not health['restart_required']
                observed=await namespace['inspect_outputs'](session,'fresh_process_reopen')
                prior=journey['first_public_readback']
                assert observed==(prior['inventory'],prior['samples'])
                await namespace['inspect_saved_case'](session,'fresh_process_reopen')
        original.validate(freeze)
        assert {str(p):sha(p) for p in immutable_paths}==immutable
        after=inventory(); assert after==receipt['output_files_before']
        receipt['output_files_after']=after
        receipt['accepted']=True
    except BaseException as error:
        receipt['failure']={'type':type(error).__name__,'message':str(error),'traceback':traceback.format_exc()}
        raise
    finally:
        receipt['reader_processes_terminal']=all(child.returncode is not None for child in children)
        receipt['reader_returncodes']=[child.returncode for child in children]
        save()
asyncio.run(readback())
