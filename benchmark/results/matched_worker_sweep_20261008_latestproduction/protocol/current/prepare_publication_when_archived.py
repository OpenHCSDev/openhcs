"""Consume the completed archive through existing figure and document owners."""
import json,os,shutil,subprocess,sys,time
from pathlib import Path
import psutil
root=Path(__file__).parent
source=Path('/home/ts/code/projects/openhcs-materialization-plumbing')
head='3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9'
assert (root/'archive-terminal.json').exists()
assert json.loads((root/'archive-terminal.json').read_text())['returncode']==0
assert json.loads((root/'terminal.json').read_text())=={'returncode':0,'source_head':head}
assert not subprocess.check_output(['git','status','--porcelain'],cwd=source,text=True).strip()
subprocess.run(['git','fetch','origin','main'],cwd=source,check=True)
changes=subprocess.check_output(['git','diff','--name-only',head,'origin/main'],cwd=source,text=True).splitlines()
assert all(path.startswith(('paper/','benchmark/results/')) or path == '.github/workflows/integration-tests.yml' for path in changes),changes
subprocess.run(['git','switch','--detach','origin/main'],cwd=source,check=True)
publication_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip()
record=source/'benchmark/results/matched_worker_sweep_20261008_latestproduction'
assert not record.exists()
shutil.copytree(root/'publication/record',record)
def run(args,env=None):
 print('Running',args,flush=True)
 subprocess.run(args,cwd=source,env=env,check=True)
run([sys.executable,str(record/'protocol/render_sweep.py'),'--record',str(record),'--protocol-manifest',str(record/'protocol/current/protocol-manifest.json'),'--output-dir',str(source/'paper/figures/slas/benchmark-publication')])
env=dict(os.environ,PYTHONPATH=str(source/'paper/figures')+os.pathsep+str(source),MPLBACKEND='Agg',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1')
run([sys.executable,'-c','from pathlib import Path; from build_slas_benchmark_reference import build_reference_figures; build_reference_figures(Path("paper/figures/slas/benchmark-publication"), Path("paper/figures/slas/benchmark-publication/reference-layout"), rebuild_coverage=False)'],env)
run([sys.executable,'-c','from build_slas_supplement import benchmark_publication; benchmark_publication()'],env)
run([sys.executable,str(root/'update_manuscript.py')])
run(['/home/ts/.local/state/openhcs-maintenance/20261005/paper-build-env/bin/python',str(source/'paper/build_paper.py'),'build','--candidate'])
(root/'publication-preparation-terminal.json').write_text(json.dumps({'returncode':0,'production_source':head,'publication_base':publication_head,'record':str(record),'review_before_commit_and_push':True},indent=2)+'\n')
print('Publication artifacts and paired candidate build ready for review; no commit or push performed',flush=True)
