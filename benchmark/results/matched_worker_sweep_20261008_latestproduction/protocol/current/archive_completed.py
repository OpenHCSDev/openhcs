"""Assemble the complete current-production sweep using existing owners and records."""
import hashlib,json,os,shutil,subprocess,sys,tarfile
from pathlib import Path
root=Path(__file__).parent;source=Path('/home/ts/code/projects/openhcs-materialization-plumbing');head='3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9'
original=source/'benchmark/results/matched_worker_sweep_20261007_exportfixed'
declaration=json.loads((original/'protocol/v6/protocol-manifest.json').read_text());modes=declaration['modes']
terminal=json.loads((root/'terminal.json').read_text());assert terminal=={'returncode':0,'source_head':head}
record=root/'publication/record';assert not record.exists()
converter=original/'protocol/v2/convert_matched_reports.py'
args=[sys.executable,str(original/'protocol/v2/archive_converted_modes.py'),str(root/'publication'),str(original/'protocol/v2/official30-manifest.json'),str(converter)]
for m in modes:
 if (m['assignments'],m['openhcs_workers']) in ((12,1),(12,4)):continue
 name=m['archive_mode'];capture=root/(name+'-strict-one-core' if name=='singlewell' else name)
 assert json.loads((capture/'terminal.json').read_text())['returncode']==0
 shutil.copyfile(root/('receive_strict_singlecore.py' if name=='singlewell' else 'receive.py'),capture/'controller.py')
 args.extend([name,str(capture)])
subprocess.run(args,cwd=source,env=dict(os.environ,ARCHIVE_ROOT=str(record)),check=True)
for m in modes:
 if (m['assignments'],m['openhcs_workers']) in ((12,1),(12,4)):continue
 name=m['archive_mode'];capture=root/(name+'-strict-one-core' if name=='singlewell' else name)
 shutil.copyfile(capture/'recipe.json',record/'protocol'/name/'recipe.json')
reused=root/'reused-published-record';reused.mkdir()
prefix='benchmark/results/matched_fixed12_physical_facts_20261008'
archive=subprocess.check_output(['git','archive','origin/main',prefix],cwd=source)
import io
with tarfile.open(fileobj=io.BytesIO(archive)) as tf:tf.extractall(reused,filter='data')
prior=reused/prefix
for m in modes:
 name=m['archive_mode']
 if (m['assignments'],m['openhcs_workers']) in ((12,1),(12,4)):
  for a,b in [('data/'+name,'data/first_use/'+name),('reports/'+name,'reports/'+name),('protocol/'+name,'protocol/'+name)]:shutil.copytree(prior/a,record/b)
for name in ('protocol/render_sweep.py',):
 destination=record/name;destination.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(root/'publication-renderer.py',destination)
shutil.copytree(original/'calibration/cold_first',record/'calibration/cold_first')
# Preserve the original native calibration attachment, not new target observations.
shutil.copytree(original/'diagnostics/native-full30-calibration',record/'diagnostics/native-full30-calibration')
new={k:v for k,v in declaration.items() if k not in ('purpose','source_revision','capture_root','artifact_worktree','production_worktree','modes','status','record_name')}
new.update({'purpose':'Complete latest-production seven-mode publication. Five newly measured modes, including a strict CPU5 single-sample follow-up, plus immutable existing fixed12 one/four-worker captures on identical production source. Genuine native CP1/CP8 and original projection calibration retained.','source_revision':head,'capture_root':str(root),'artifact_worktree':str(source),'production_worktree':str(source),'status':'QUALIFIED_CURRENT_PRODUCTION_SWEEP','record_name':'matched_worker_sweep_20261008_latestproduction','modes':[]})
for m in modes:
 name=m['archive_mode'];custody=json.loads((record/'data/first_use'/name/'summary_custody.json').read_text());assert custody['status']=='PASS' and custody['source_head']==head and len(custody['cases'])==30
 descriptor={k:m[k] for k in ('archive_mode','assignments','openhcs_workers','native_processes','target_native_observation_count','first_use_archive_mode')}
 descriptor['capture_origin']='reused immutable fixed12 capture' if (m['assignments'],m['openhcs_workers']) in ((12,1),(12,4)) else 'new missing-mode capture'
 new['modes'].append(descriptor)
(record/'protocol/current/protocol-manifest.json').parent.mkdir(parents=True);(record/'protocol/current/protocol-manifest.json').write_text(json.dumps(new,indent=2)+'\n')
shutil.copyfile(root/'plan.json',record/'protocol/current/refresh-plan.json')
for name in ('receive.py','receive_strict_singlecore.py','complete_strict_and_publish.py','prepare_publication_when_archived.py','update_manuscript.py','run.py','qualify_missing.py','archive_completed.py','source-and-environment.json','terminal.json'):
 shutil.copyfile(root/name,record/'protocol/current'/name)
shutil.copytree(root/'publication/singlewell-initial-wider-worker-affinity',record/'diagnostics/singlewell-initial-wider-worker-affinity')
shutil.copyfile(root/'publication-readme.md',record/'README.md')
files={str(p.relative_to(record)):hashlib.file_digest(p.open('rb'),'sha256').hexdigest() for p in record.rglob('*') if p.is_file()}
(record/'archive_custody.json').write_text(json.dumps({'source_head':head,'status':'PASS','case_count':30,'mode_count':7,'files':files},indent=2)+'\n')
print('Complete seven-mode archive assembled:',record)
