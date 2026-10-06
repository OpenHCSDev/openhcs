import csv
import json
import os
import subprocess
import time
from pathlib import Path

root = Path('/home/ts/code/projects/openhcs')
runs = root.parent / 'openhcs-benchmark-runs'
python = root / '.venv/bin/python'
observations = []
for number, (name, package) in enumerate((
    ('main', root), ('candidate', Path('/tmp/openhcs-source-header-current-main-installed-20260930')),
    ('candidate', Path('/tmp/openhcs-source-header-current-main-installed-20260930')), ('main', root),
), 1):
    out = runs / f'perf-source-header-current-main-primary-abba-{number}-{name}-20260930'
    command = [str(python), str(root / 'scripts/benchmark_cppipe_well_throughput.py'),
        '--manifest', str(root / 'benchmark/manifests/official30_portable_axis1.json'),
        '--output-dir', str(out), '--mode', '1w_1t', '--case', 'cp_tutorial_3d_monolayer',
]
    env = dict(os.environ, PYTHONPATH=str(package), OPENHCS_CPU_ONLY='true',
        NUMBA_CACHE_DIR='/tmp/openhcs-source-identity-shared-cache-20260930')
    start = time.perf_counter()
    with out.with_suffix('.log').open('w') as stream:
        result = subprocess.run(['/usr/bin/taskset', '-c', '5', *command], env=env,
            cwd='/tmp', stdout=stream, stderr=subprocess.STDOUT)
    clock = {'returncode': result.returncode, 'cli_seconds': time.perf_counter() - start,
        'command': command, 'package': str(package)}
    out.with_name(out.name + '-clock.json').write_text(json.dumps(clock, indent=2) + '\n')
    assert result.returncode == 0, clock
    rows = list(csv.DictReader((out / 'well_throughput.csv').open()))
    assert len(rows) == 1 and all(row['status'] == 'success' and row['successful_wells'] == '1' for row in rows), rows
    observations.append({'number': number, 'package': name, 'directory': str(out), 'rows': rows})
    (runs / 'perf-source-header-current-main-primary-abba-observations-20260930.json').write_text(json.dumps(observations, indent=2) + '\n')
    print(json.dumps({'number': number, 'package': name, 'rows': [{k: row[k] for k in
        ('case_name', 'compile_seconds', 'execute_seconds', 'total_seconds', 'status')} for row in rows]}), flush=True)
