import csv
import json
import os
import subprocess
from pathlib import Path

root = Path('/home/ts/code/projects/openhcs')
runs = root.parent / 'openhcs-benchmark-runs'
for name, package in (('main', root), ('candidate', Path('/tmp/openhcs-source-header-installed-20260930'))):
    timing = runs / f'perf-source-header-preparation-timing-{name}-20260930'
    timing.mkdir()
    out = runs / f'perf-source-header-preparation-production-{name}-20260930'
    env = dict(os.environ,
        PYTHONPATH=f'/tmp/openhcs-source-header-timing-site-20260930:{package}',
        OPENHCS_SOURCE_PREPARATION_TIMING_DIR=str(timing), OPENHCS_SOURCE_HEADER_VARIANT=name, OPENHCS_CPU_ONLY='true',
        NUMBA_CACHE_DIR='/tmp/openhcs-source-identity-shared-cache-20260930')
    command = ['/usr/bin/taskset', '-c', '5', str(root / '.venv/bin/python'),
        str(root / 'scripts/benchmark_cppipe_well_throughput.py'), '--manifest',
        str(root / 'benchmark/manifests/official30_portable_axis1.json'), '--mode', '1w_1t',
        '--case', 'cp_tutorial_3d_monolayer', '--output-dir', str(out)]
    with out.with_suffix('.log').open('w') as stream:
        result = subprocess.run(command, env=env, cwd='/tmp', stdout=stream, stderr=subprocess.STDOUT)
    assert result.returncode == 0, (name, result.returncode)
    rows = list(csv.DictReader((out / 'well_throughput.csv').open()))
    assert len(rows) == 1 and rows[0]['status'] == 'success' and rows[0]['successful_wells'] == '1', rows
    print(json.dumps({'package': name, 'rows': rows}), flush=True)
