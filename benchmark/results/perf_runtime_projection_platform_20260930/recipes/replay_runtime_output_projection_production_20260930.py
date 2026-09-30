import json,pickle,time,statistics,sys
from pathlib import Path
import numpy as np
from openhcs.core.runtime_image_values import image_payload_data,image_payload_mask,image_payload_metadata
variant=sys.argv[1]
if variant=='main':
 from openhcs.core.aligned_image_payload import flatten_aligned_image_payload_slices,flatten_aligned_image_slice_contexts
 def project(value):return flatten_aligned_image_payload_slices(value),flatten_aligned_image_slice_contexts(value)
else:
 def project(value):
  paired=tuple(value.projected_output_slices())
  return tuple(p for p,c in paired),tuple(c for p,c in paired) if value.slice_contexts else ()
runs=Path('/home/ts/code/projects/openhcs-benchmark-runs');folder=runs/'perf-source-header-current-runtime-profile-20260930';rows=[]
for step in (1,13,17):
 path=next(folder.glob(f'step-{step}-*_validate_and_unstack.pickle'));fixture=pickle.loads(path.read_bytes());value=fixture['processed_stack'];saved=fixture['output_data'];actual,contexts=project(value)
 assert contexts==saved.slice_contexts and len(actual)==len(saved.slices)==60
 for x,y in zip(actual,saved.slices,strict=True):
  assert image_payload_metadata(x)==image_payload_metadata(y)
  np.testing.assert_array_equal(image_payload_data(x),image_payload_data(y))
  xm=image_payload_mask(x);ym=image_payload_mask(y)
  if xm is None:assert ym is None
  else:np.testing.assert_array_equal(xm,ym)
 samples=[]
 for _ in range(7):
  start=time.perf_counter();project(value);samples.append(time.perf_counter()-start)
 rows.append({'step':step,'fixture':str(path),'exact_saved_output_parity':True,'samples':samples,'median_seconds':statistics.median(samples)})
(runs/f'perf-runtime-output-projection-production-{variant}-20260930.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:v for k,v in row.items() if k!='samples'} for row in rows],indent=2))
