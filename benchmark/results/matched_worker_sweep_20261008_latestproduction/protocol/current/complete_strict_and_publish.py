"""Finish strict one-core follow-up and consume the complete qualified sweep."""
import json,os,shutil,subprocess,sys,time
from pathlib import Path
root=Path(__file__).parent
source=Path('/home/ts/code/projects/openhcs-materialization-plumbing')
head='3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9'
while True:
 terminal=root/'terminal.json'
 if terminal.exists():
  result=json.loads(terminal.read_text())
  if result['returncode']!=0:raise RuntimeError(result)
  if 'All five missing configurations scientifically and clock-qualified' in (root/'qualification.log').read_text():break
 time.sleep(5)
env=dict(os.environ);env.update(json.loads((root/'source-and-environment.json').read_text())['environment'])
with (root/'singlewell-strict-one-core.log').open('w') as log:
 subprocess.run(['taskset','-c','2-5',sys.executable,'-u',str(root/'receive_strict_singlecore.py'),'--assignments','1','--workers','1','--expected-source-head',head],cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
previous=root/'publication/data/first_use/singlewell'
shutil.move(previous,root/'publication/singlewell-initial-wider-worker-affinity')
converter=source/'benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v2/convert_matched_reports.py'
subprocess.run(['taskset','-c','0,1',sys.executable,str(converter),'--suite-dir',str(root/'singlewell-strict-one-core'),'--output-dir',str(previous)],cwd=source,check=True)
subprocess.run([sys.executable,str(root/'archive_completed.py')],cwd=source,check=True)
(root/'archive-terminal.json').write_text(json.dumps({'returncode':0,'record':str(root/'publication/record')},indent=2)+'\n')
subprocess.run([sys.executable,str(root/'prepare_publication_when_archived.py')],cwd=source,check=True)
print('Complete publication preparation ready for review',flush=True)
