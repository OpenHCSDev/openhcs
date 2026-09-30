from pathlib import Path
import pickle,json,time,sys
import numpy as np
from mahotas.features.texture import haralick_features
sys.path.insert(0,'/home/ts/code/projects/openhcs-compile-perf')
from openhcs.processing.backends.cellprofiler.texture import _haralick_features_numba
root=Path('/home/ts/code/projects/openhcs-benchmark-runs/perf-haralick-frontier-20260929');rows=pickle.loads((root/'matrices_and_features.pkl').read_bytes())
start=time.perf_counter();_haralick_features_numba(rows[0][0],False);preparation=time.perf_counter()-start
maximum=production_maximum=0.;different_calls=0
for i,(cmats,args,kwargs,expected) in enumerate(rows):
 before=cmats.copy();actual=_haralick_features_numba(cmats,bool(kwargs.get('ignore_zeros',False)))
 np.testing.assert_allclose(actual,expected,rtol=1e-6,atol=1e-6)
 np.testing.assert_array_equal(cmats,before)
 delta=float(np.max(np.abs(actual-expected)));maximum=max(maximum,delta)
 if i>=2:production_maximum=max(production_maximum,delta)
 different_calls+=not np.array_equal(actual,expected)
samples=[]
for name in ['mahotas','fused']*4:
 start=time.perf_counter()
 for cmats,args,kwargs,expected in rows:
  if name=='mahotas':actual=haralick_features(cmats.copy(),**kwargs)
  else:actual=_haralick_features_numba(cmats,bool(kwargs.get('ignore_zeros',False)))
 samples.append(dict(implementation=name,seconds=time.perf_counter()-start,calls=len(rows)))
report=dict(preparation_seconds=preparation,saved_calls=len(rows),production_calls=len(rows)-2,maximum_absolute_difference=maximum,production_maximum_absolute_difference=production_maximum,different_calls=different_calls,numeric_abs_tolerance=1e-6,numeric_rel_tolerance=1e-6,source='/benchmark/adapters/openhcs.py::_strict_cellprofiler_runtime_equivalence_policy',input_unchanged=True,samples=samples)
(root/'production_fused_feature_replays.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
