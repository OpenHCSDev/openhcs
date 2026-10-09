"""Unlaunched receiving recipe: normal matched jobs, one owned persistent server."""
import sys,json,subprocess,os,time
import psutil
from pathlib import Path
from dataclasses import replace
SOURCE=Path('/home/ts/code/projects/openhcs-materialization-plumbing')
sys.path.insert(0,str(SOURCE))
import openhcs.core
from benchmark.runtime_env import configure_headless_cpu_benchmark_runtime
configure_headless_cpu_benchmark_runtime('WARNING')
import openhcs.runtime.zmq_config as config
config.OPENHCS_ZMQ_CONFIG=replace(config.OPENHCS_ZMQ_CONFIG,client_connect_timeout_seconds=180.0)
from benchmark import matched_cellprofiler_batch as driver
from zmqruntime import DataControlPortPairAuthority
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
HERE=Path(__file__).resolve().parent
WORKERS=int(sys.argv[sys.argv.index('--workers')+1])
ASSIGNMENTS=int(sys.argv[sys.argv.index('--assignments')+1])
assert (ASSIGNMENTS, WORKERS) in ((1,1),(8,2),(12,2),(12,3),(16,4))
assert '--expected-source-head' in sys.argv
expected=sys.argv[sys.argv.index('--expected-source-head')+1]
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=SOURCE,text=True).strip()
assert head==expected,(head,expected)
assert not subprocess.check_output(['git','status','--porcelain'],cwd=SOURCE,text=True).strip(),'Source must be clean'
MODE='singlewell' if ASSIGNMENTS == 1 else f'{ASSIGNMENTS}assignments-{WORKERS}workers'
root=HERE/(MODE+'-affinity-corrected' if ASSIGNMENTS == 1 else MODE);root.mkdir(exist_ok=False)
common=['--manifest',str(SOURCE/'benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v2/official30-manifest.json'),'--well-count','1','--repeat-assignments',str(ASSIGNMENTS),'--native-jobs','1','--repetitions','3','--native-python','/home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python','--candidate-only','--production-source-root',str(SOURCE),'--native-reference-root',('/home/ts/.local/state/openhcs-maintenance/20261007/issue1100-matched-sweep-v1/1assignment-1worker/capture/cases' if ASSIGNMENTS == 1 else '/home/ts/.local/state/openhcs-maintenance/20261007/issue1100-matched-sweep-v1/retained-native8-complete-v1'),'--native-measurement-cache-root',str(HERE/'native-measurement-facts'),'--comparison-workers','2','--comparison-cpus','0','1']
if ASSIGNMENTS <= 8:
 common.remove('--candidate-only')
if ASSIGNMENTS == 1:
 i=common.index('--repeat-assignments');del common[i:i+2]
 i=common.index('--comparison-workers');common[i+1]='1'
 i=common.index('--comparison-cpus');del common[i:i+3]
if ASSIGNMENTS > 8:
 common.extend(['--native-execution-model','retained-first-batch-plus-warm-assignments-v1'])
command={'source_freeze_head':head,'argv':common+['--openhcs-workers',str(WORKERS),'--all-cases','--output-dir',str(root/'cases')]}
(root/'command.json').write_text(json.dumps(command,indent=2))
cases=tuple(case.name for case in driver.load_comparison_cases(SOURCE/'benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v2/official30-manifest.json'))
assert len(cases)==30 and len(set(cases))==30
port=DataControlPortPairAuthority.acquire(config.OPENHCS_ZMQ_CONFIG,transport_mode=config.OPENHCS_ZMQ_CONFIG.transport_mode).data_port
assert os.environ.get('NUMPY_MADVISE_HUGEPAGE') == '0'
import numpy as np
assert np._core.multiarray._get_madvise_hugepage() is False
recipe={'numpy_hugepage_advice':'0 (production startup default; inherited by owned server and fork workers)', 'source':head,'scope':f'Full30 {ASSIGNMENTS}assignment/{WORKERS}worker capture; warmup+3 actualOH with fresh parity; matching retained CP1/CP8 untouched; CP12/16 projection only in reporting','common_argv':common,'cases':cases,'prepared_worker_startup':'Latest merged production main3b173; readiness before pipeline clocks; endpoint per mode; parent pre-READY affinity2-5','server_port':port,'affinity_by_job':[]}
(root/'recipe.json').write_text(json.dumps(recipe,indent=2))
assert set(os.sched_getaffinity(0)) == {2,3,4,5}, 'Prepared workers must inherit four CPUs before READY'
with ZMQExecutionClient(port=port,persistent=False) as client:
 for workers in (WORKERS,):
  endpoint=client.connected_endpoint
  assert endpoint is not None and endpoint.process_identity is not None
  identity=endpoint.process_identity
  process=psutil.Process(identity.pid)
  assert abs(process.create_time()-identity.create_time)<.001,'Endpoint incarnation differs'
  cpus={5} if workers==1 else {2,3,4,5}
  for thread in process.threads():os.sched_setaffinity(thread.id,cpus)
  threads={str(thread.id):sorted(os.sched_getaffinity(thread.id)) for thread in process.threads()}
  assert all(set(value)==cpus for value in threads.values()),threads
  children=process.children(recursive=False)
  assert len(children)==4,[(p.pid,p.cmdline()) for p in children]
  child_affinities={str(p.pid):p.cpu_affinity() for p in children}
  assert all(set(v)=={2,3,4,5} for v in child_affinities.values()),child_affinities
  recipe['prepared_children_affinity']=child_affinities
  recipe['affinity_by_job'].append({'workers':workers,'epoch_seconds':time.time(),'endpoint_pid':identity.pid,'endpoint_create_time':identity.create_time,'parent_cpu_affinity':sorted(os.sched_getaffinity(0)),'server_cpu_affinity':sorted(os.sched_getaffinity(identity.pid)),'server_thread_cpu_affinity':threads})
  (root/'recipe.json').write_text(json.dumps(recipe,indent=2))
  if ASSIGNMENTS == 1: os.sched_setaffinity(0,{5})
  print('Starting workers',workers,'endpoint',identity.pid,'server affinity',sorted(cpus),flush=True)
  for case in cases:
   args=driver._parser().parse_args(common+['--case',case,'--openhcs-workers',str(workers),'--output-dir',str(root/'cases'/case)])
   driver._run_case(args,client)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=SOURCE,text=True).strip()==head
assert not subprocess.check_output(['git','status','--porcelain'],cwd=SOURCE,text=True).strip()
(root/'terminal.json').write_text(json.dumps({'returncode':0,'source_head':head,'source_head_before':head,'source_head_after':head,'source_status_after':''},indent=2))
