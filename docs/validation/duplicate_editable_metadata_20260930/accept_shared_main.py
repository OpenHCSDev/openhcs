import csv
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

import numpy as np
import tifffile
import openhcs.core.aligned_image_payload as aligned
import importlib.metadata as metadata
active = [d for d in metadata.distributions() if d._path.name.startswith('openhcs')]
assert len(active) == 1 and active[0].version == '0.8.7'
subprocess.run([os.sys.executable, '-m', 'pip', 'check'], cwd='/tmp', check=True)

root = Path('/home/ts/code/projects/openhcs')
runs = root.parent / 'openhcs-benchmark-runs'
out = runs / 'perf-runtime-projection-shared-main-clean-acceptance-20260930'
cache = Path('/tmp/openhcs-runtime-projection-shared-main-clean-fresh-cache-20260930')
assert not out.exists() and not cache.exists()
assert Path(aligned.__file__).resolve() == root / 'openhcs/core/aligned_image_payload.py'
assert aligned.ImageOutputBundle.projected_output_slices is aligned.AlignedImageStack.projected_output_slices
commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
assert commit == '12e6f3b25a659bba8d8f7d3f4709db991c97000d'
env = dict(os.environ, OPENHCS_CPU_ONLY='true', NUMBA_CACHE_DIR=str(cache))
env.pop('PYTHONPATH', None)
command = ['/usr/bin/taskset', '-c', '5', str(root / '.venv/bin/python'),
           str(root / 'scripts/benchmark_cppipe_well_throughput.py'), '--manifest',
           str(root / 'benchmark/manifests/official30_portable_axis1.json'), '--mode',
           '1w_1t', '--case', 'cp_tutorial_3d_monolayer', '--output-dir', str(out)]
started = time.perf_counter()
with out.with_suffix('.log').open('w') as stream:
    result = subprocess.run(command, cwd='/tmp', env=env, stdout=stream, stderr=subprocess.STDOUT)
cli_seconds = time.perf_counter() - started
assert result.returncode == 0, result.returncode
rows = list(csv.DictReader((out / 'well_throughput.csv').open()))
assert len(rows) == 1 and rows[0]['status'] == 'success' and rows[0]['successful_wells'] == '1', rows
suffix = Path('cp_tutorial_3d_monolayer/wells_1/workers_1/images_3d_monolayer_final_source_workspace_well_throughput')
folder = out / suffix
control = runs / 'perf-plate-transport-full-candidate-20260929' / suffix
csvs = sorted((folder / 'results').glob('*.csv'))
assert {p.name for p in csvs} == {p.name for p in (control / 'results').glob('*.csv')}
for p in csvs:
    assert p.read_bytes() == (control / 'results' / p.name).read_bytes(), p
images = sorted((folder / 'images').glob('*Labels.tiff'))
assert {p.name for p in images} == {p.name for p in (control / 'images').glob('*Labels.tiff')}
for p in images:
    actual, expected = tifffile.imread(p), tifffile.imread(control / 'images' / p.name)
    assert actual.dtype == expected.dtype and actual.shape == expected.shape and np.array_equal(actual, expected), p
assert len(csvs) == 6 and len(images) == 120
report = {'source_commit': commit, 'source_module': aligned.__file__, 'command': command,
          'rows': rows, 'cli_seconds_separate_from_pipeline': cli_seconds,
          'fresh_kernel_cache': str(cache), 'PYTHONPATH': 'unset',
          'exact_csv_count': len(csvs), 'exact_label_image_count': len(images),
          'csv_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in csvs},
          'limits': 'Shared editable main, fresh cache before mandatory server prewarm; preparation before readiness, fork workers; server startup/shutdown excluded from pipeline clocks. Distinct acceptance, not pooled with warm-cache ABBA.'}
(runs / 'perf-runtime-projection-shared-main-clean-acceptance-20260930.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2), flush=True)
