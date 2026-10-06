from pathlib import Path
from contextlib import ExitStack
import argparse,fcntl,json,subprocess,os,hashlib
HERE=Path(__file__).resolve().parent
SOURCE=Path('/home/ts/.local/state/openhcs-maintenance/20261004/intensity-batch-maxima-source')
BASE=Path('/home/ts/.local/state/openhcs-maintenance/20261005')
parser=argparse.ArgumentParser()
parser.add_argument('--source-head',required=True)
args=parser.parse_args()
command=json.loads((HERE/'command.json').read_text())
assert command['status']=='PREPARED_FINAL_COHORT_NOT_LAUNCHED', 'Replace provisional cohort from qualified full30 frontier before launching'
assert command['source_freeze_head'] in (None,args.source_head), 'Prepared packet already belongs to another source'
command['source_freeze_head']=args.source_head
assert not (HERE/'suite.log').exists(), 'Existing capture must never be overwritten'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=SOURCE,text=True).strip()
assert head==command['source_freeze_head']
assert not subprocess.check_output(['git','status','--porcelain'],cwd=SOURCE,text=True).strip()
env=json.loads((BASE/'parameter-owner-illum3-default-ordinary-v1/private-launch-environment.json').read_text())
env={k:v for k,v in env.items() if not k.startswith(('OPENHCS_PROFILE_','OPENHCS_DIAGNOSTIC_')) and k not in ('OPENHCS_WORKER_PROFILE_DIR','OPENHCS_PRIVATE_BACKING_CENSUS')}
env.update(PYTHONPATH=str(SOURCE),PYTHONDONTWRITEBYTECODE='1',NUMBA_CACHE_DIR=str(BASE/'final-official30-singlewell-matched-v1/numba-cache'))
def sealed_inputs():
 return {'environment':env,'installed_packages':subprocess.check_output(['/home/ts/code/projects/openhcs/.venv/bin/python','-m','pip','freeze','--all'],text=True),'native_binary_sha256':{str(path.relative_to(SOURCE)):hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted((SOURCE/'openhcs').rglob('*.so'))}}
leases=tuple(dict.fromkeys((Path('/home/ts/.cache/openhcs/official30-runtime.lock'),Path(env['XDG_CACHE_HOME'])/'openhcs/official30-runtime.lock')))
with ExitStack() as stack:
 for path in leases:
  path.parent.mkdir(parents=True,exist_ok=True)
  lock=stack.enter_context(path.open('a+'));fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 seal=sealed_inputs()
 (HERE/'environment-source-seal.json').write_text(json.dumps(seal,indent=2)+'\n')
 log=stack.enter_context((HERE/'suite.log').open('xb'))
 (HERE/'command.json').write_text(json.dumps(command,indent=2)+'\n')
 child=subprocess.Popen(command['argv'],cwd=SOURCE,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
 (HERE/'child.json').write_text(json.dumps({'pid':child.pid,'source_head':head},indent=2)+'\n')
 print('SUITE_LIVE',child.pid,head,flush=True)
 observer= subprocess.Popen(['taskset','-c','0', '/usr/bin/python', str(HERE.parents[1]/'sample.py'), str(child.pid),str(os.getpid()),str(HERE/'passive-process-samples.jsonl')],stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
 code=child.wait()
 observer.wait()
 assert sealed_inputs()==seal, 'Installed environment/native binary changed during capture'
 terminal={'returncode':code,'source_head_before':head,'source_head_after':subprocess.check_output(['git','rev-parse','HEAD'],cwd=SOURCE,text=True).strip(),'source_status_after':subprocess.check_output(['git','status','--porcelain'],cwd=SOURCE,text=True)}
 (HERE/'terminal.json').write_text(json.dumps(terminal,indent=2)+'\n')
 print('SUITE_TERMINAL',code,flush=True)
