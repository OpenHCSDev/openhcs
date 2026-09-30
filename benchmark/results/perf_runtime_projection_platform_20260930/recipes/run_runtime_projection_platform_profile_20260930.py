import os,subprocess,csv,json
from pathlib import Path
root=Path('/home/ts/code/projects/openhcs');runs=root.parent/'openhcs-benchmark-runs'
out=runs/'perf-runtime-projection-platform-profile-production-20260930'
cmd=['/usr/bin/taskset','-c','5',str(root/'.venv/bin/python'),str(root/'scripts/benchmark_cppipe_well_throughput.py'),'--manifest',str(root/'benchmark/manifests/official30_portable_axis1.json'),'--mode','1w_1t','--case','cp_tutorial_3d_monolayer','--output-dir',str(out)]
env=dict(os.environ,PYTHONPATH='/tmp/openhcs-runtime-projection-platform-site-20260930:/tmp/openhcs-runtime-projection-current-main-installed-20260930',OPENHCS_CPU_ONLY='true',NUMBA_CACHE_DIR='/tmp/openhcs-source-identity-shared-cache-20260930')
with out.with_suffix('.log').open('w') as stream: result=subprocess.run(cmd,cwd='/tmp',env=env,stdout=stream,stderr=subprocess.STDOUT)
assert result.returncode==0,result.returncode
rows=list(csv.DictReader((out/'well_throughput.csv').open()));assert len(rows)==1 and rows[0]['status']=='success' and rows[0]['successful_wells']=='1',rows
print(json.dumps(rows))
