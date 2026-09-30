import json, hashlib, statistics
from pathlib import Path
import numpy as np
import tifffile
runs=Path('/home/ts/code/projects/openhcs-benchmark-runs')
observations=json.loads((runs/'perf-source-header-current-main-primary-abba-observations-20260930.json').read_text())
control=runs/'perf-plate-transport-full-candidate-20260929/cp_tutorial_3d_monolayer/wells_1/workers_1/images_3d_monolayer_final_source_workspace_well_throughput'
parity=[]
for obs in observations:
 folder=Path(obs['directory'])/'cp_tutorial_3d_monolayer/wells_1/workers_1/images_3d_monolayer_final_source_workspace_well_throughput'
 csvs=sorted((folder/'results').glob('*.csv'))
 assert {p.name for p in csvs}=={p.name for p in (control/'results').glob('*.csv')}
 for p in csvs: assert p.read_bytes()==(control/'results'/p.name).read_bytes(),p
 images=sorted((folder/'images').glob('*Labels.tiff'))
 assert {p.name for p in images}=={p.name for p in (control/'images').glob('*Labels.tiff')}
 for p in images:
  x=tifffile.imread(p); y=tifffile.imread(control/'images'/p.name)
  assert x.dtype==y.dtype and x.shape==y.shape and np.array_equal(x,y),p
 assert len(csvs)==6 and len(images)==120
 parity.append({'directory':obs['directory'],'csv_byte_parity':[{'name':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in csvs],'exact_label_images':len(images)})
means={name:{key:statistics.mean(float(row[key]) for obs in observations if obs['package']==name for row in obs['rows']) for key in ('compile_seconds','execute_seconds','total_seconds')} for name in ('main','candidate')}
report={'parity':parity,'means':means,'count_per_version':2,'limits':'Current main a2858341a, candidate cf1f5a4025, all recorded current main dependency pins. CPU5, 1w_1t, warm shared on-disk kernel cache; mandatory preparation before server readiness; fork workers; pipeline clocks exclude server startup/shutdown. Four unprofiled observations, no overlap with our audits/tests/builds or other benchmarks. Do not pool with earlier dependency/measurement protocols.'}
(runs/'perf-source-header-current-main-comparison-20260930.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'means':means,'observations':len(parity),'csvs':len(parity)*6,'labels':len(parity)*120},indent=2))
