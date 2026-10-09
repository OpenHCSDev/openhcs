"""Run the existing scientific/clock qualifier on completed missing modes."""
import json,subprocess,sys,time
from pathlib import Path
root=Path(__file__).parent;source=Path('/home/ts/code/projects/openhcs-materialization-plumbing')
converter=source/'benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v2/convert_matched_reports.py'
manifest=json.loads((source/'benchmark/results/matched_worker_sweep_20261007_exportfixed/protocol/v6/protocol-manifest.json').read_text())
for mode in manifest['modes']:
 if (mode['assignments'],mode['openhcs_workers']) in ((12,1),(12,4)):continue
 name=mode['archive_mode'];capture=root/(name+'-affinity-corrected' if name=='singlewell' else name)
 while not (capture/'terminal.json').exists():
  if (root/'terminal.json').exists() and json.loads((root/'terminal.json').read_text())['returncode'] != 0:
   raise RuntimeError('Capture terminated before requested mode completed')
  time.sleep(5)
 terminal=json.loads((capture/'terminal.json').read_text());assert terminal['source_head']=='3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9' and terminal['returncode']==0
 destination=root/'publication/data/first_use'/name
 if destination.exists():
  admitted=json.loads((destination/'summary_custody.json').read_text())
  assert admitted['status']=='PASS' and admitted['source_head']==terminal['source_head']
  import hashlib
  assert admitted['suite_terminal']['sha256']==hashlib.file_digest((capture/'terminal.json').open('rb'),'sha256').hexdigest()
  assert admitted['converter_sha256']==hashlib.file_digest(converter.open('rb'),'sha256').hexdigest()
  continue
 args=['taskset','-c','0,1',sys.executable,str(converter),'--suite-dir',str(capture),'--output-dir',str(destination)]
 if mode['assignments']>1:args.append('--scaling')
 subprocess.run(args,cwd=source,check=True)

print('All five missing configurations scientifically and clock-qualified',flush=True)
