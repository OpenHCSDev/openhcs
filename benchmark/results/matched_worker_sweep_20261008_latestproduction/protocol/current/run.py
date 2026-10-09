import os,sys,subprocess,json,shutil
from pathlib import Path
root=Path(__file__).resolve().parent
source=Path('/home/ts/code/projects/openhcs-materialization-plumbing')
head='3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9'
env=dict(os.environ)
env.update(json.loads((root/'source-and-environment.json').read_text())['environment'])
preflight=json.loads((root/'all30/native_reference_preflight_suite.json').read_text())
assert preflight['status']=='PASS' and preflight['processing_executed'] is False and len(preflight['cases'])==30
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()==head
assert not subprocess.check_output(['git','status','--porcelain'],cwd=source,text=True).strip()
for assignments,workers in ((1,1),(8,2),(12,2),(12,3),(16,4)):
 name='singlewell' if assignments==1 else f'{assignments}assignments-{workers}workers'
 if shutil.disk_usage(root).free < 5*2**30:raise RuntimeError('Insufficient home space for next mode')
 with (root/(name+'.log')).open('w') as log:
  r=subprocess.run(['taskset','-c','2-5',sys.executable,'-u',str(root/'receive.py'),'--assignments',str(assignments),'--workers',str(workers),'--expected-source-head',head],cwd=source,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
  if r.returncode:
   (root/'terminal.json').write_text(json.dumps({'returncode':r.returncode,'source_head':head,'failed_mode':name},indent=2))
   raise SystemExit(r.returncode)
(root/'terminal.json').write_text(json.dumps({'returncode':0,'source_head':head},indent=2))
