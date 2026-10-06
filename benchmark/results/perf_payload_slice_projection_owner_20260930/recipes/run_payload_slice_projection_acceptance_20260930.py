import csv
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

root = Path('/home/ts/code/projects/openhcs')
candidate = root.parent / 'openhcs-compile-perf'
runs = root.parent / 'openhcs-benchmark-runs'
observations = []
for index, label in enumerate(('main', 'candidate', 'candidate', 'main')):
    source = candidate if label == 'candidate' else root
    destination = runs / f'perf-payload-slice-projection-public-abba-{index}-{label}-20260930'
    environment = dict(os.environ, PYTHONPATH=str(source), OPENHCS_CPU_ONLY='true', NUMBA_CACHE_DIR='/tmp/openhcs-source-identity-shared-cache-20260930')
    probe = subprocess.check_output([str(root / '.venv/bin/python'), '-c', 'import openhcs.core.runtime_image_values as m; print(m.__file__)'], cwd='/tmp', env=environment, text=True).strip()
    assert Path(probe).resolve() == source / 'openhcs/core/runtime_image_values.py', probe
    command = ['/usr/bin/taskset', '-c', '5', str(root / '.venv/bin/python'), str(root / 'scripts/benchmark_cppipe_well_throughput.py'), '--manifest', str(root / 'benchmark/manifests/official30_portable_axis1.json'), '--mode', '1w_1t', '--case', 'cp_tutorial_3d_monolayer', '--output-dir', str(destination)]
    started = time.perf_counter()
    with destination.with_suffix('.log').open('w') as stream:
        result = subprocess.run(command, cwd='/tmp', env=environment, stdout=stream, stderr=subprocess.STDOUT)
    assert result.returncode == 0, (label, result.returncode)
    rows = list(csv.DictReader((destination / 'well_throughput.csv').open()))
    assert len(rows) == 1 and rows[0]['status'] == 'success' and rows[0]['successful_wells'] == '1', rows
    observation = {'index': index, 'label': label, 'source': str(source), 'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source, text=True).strip(), 'runtime_import': probe, 'runtime_sha256': hashlib.sha256(Path(probe).read_bytes()).hexdigest(), 'directory': str(destination), 'rows': rows, 'cli_seconds': time.perf_counter() - started}
    observations.append(observation)
    (runs / 'perf-payload-slice-projection-public-abba-observations-20260930.json').write_text(json.dumps(observations, indent=2) + '\n')
    print(json.dumps({'index': index, 'label': label, 'rows': rows}), flush=True)
