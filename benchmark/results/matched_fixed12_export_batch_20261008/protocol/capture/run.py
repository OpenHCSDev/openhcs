import os,sys,subprocess,json,hashlib
from pathlib import Path
root=Path(__file__).resolve().parent
source=Path('/home/ts/code/projects/openhcs-materialization-plumbing')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()
assert head=='7d13c202706f7582c4ec1f4a9874a441f67dad5f'
assert not subprocess.check_output(['git','status','--porcelain'],cwd=source,text=True).strip()
preflight_root=Path('/home/ts/.local/state/openhcs-maintenance/20261008/retained-native-content-preflight-v2')
preflight=json.loads((preflight_root/'terminal.json').read_text())
assert preflight=={'returncode':0,'source_head':head,'processing_executed':False,'case_count':30}
preflight_summary=json.loads((preflight_root/'all30/native_reference_preflight_suite.json').read_text())
assert preflight_summary['status']=='PASS' and len(preflight_summary['cases'])==30
env=dict(os.environ)
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS'):env[key]='1'
env['NPY_DISABLE_CPU_FEATURES']='AVX512_SKX,X86_V4'
env['PYTHONHASHSEED']='0'
env['NUMPY_MADVISE_HUGEPAGE']='0'
(root/'source-and-environment.json').write_text(json.dumps({'source_head':head,'environment':{k:env[k] for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS','NPY_DISABLE_CPU_FEATURES','PYTHONHASHSEED','NUMPY_MADVISE_HUGEPAGE')},'native_tabular_sha256':hashlib.sha256((source/'openhcs/core/_tabular_native.abi3.so').read_bytes()).hexdigest()},indent=2))
for workers in (1,4):
 with (root/f'driver-{workers}.log').open('w') as log:
  result=subprocess.run(['taskset','-c','2-5',sys.executable,'-u',str(root/'receive.py'),'--workers',str(workers),'--expected-source-head',head],cwd=source,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
  if result.returncode:
   (root/'terminal.json').write_text(json.dumps({'returncode':result.returncode,'source_head':head,'failed_mode':str(workers)+'workers'},indent=2))
   raise SystemExit(result.returncode)
(root/'terminal.json').write_text(json.dumps({'returncode':0,'source_head':head},indent=2))
