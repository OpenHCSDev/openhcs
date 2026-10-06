import hashlib
import json
import statistics
from pathlib import Path

import numpy as np
import tifffile

runs = Path('/home/ts/code/projects/openhcs-benchmark-runs')
suffix = 'cp_tutorial_3d_monolayer/wells_1/workers_1/images_3d_monolayer_final_source_workspace_well_throughput'
control = runs / 'perf-plate-transport-full-candidate-20260929' / suffix
observations_path = runs / 'perf-payload-slice-projection-public-abba-observations-20260930.json'
observations = json.loads(observations_path.read_text()) if observations_path.exists() else []
targets = [(Path(row['directory']), row['label']) for row in observations]
targets += [(runs / 'perf-runtime-owner-timer-production-20260930', 'thread_local_direct_timer'), (runs / 'perf-runtime-whole-pattern-profile-production-20260930', 'archived_contaminated_cprofile')]
parity = []
for directory, label in targets:
    folder = directory / suffix
    csvs = sorted((folder / 'results').glob('*.csv'))
    assert {p.name for p in csvs} == {p.name for p in (control / 'results').glob('*.csv')}
    for path in csvs:
        assert path.read_bytes() == (control / 'results' / path.name).read_bytes(), path
    images = sorted((folder / 'images').glob('*Labels.tiff'))
    assert {p.name for p in images} == {p.name for p in (control / 'images').glob('*Labels.tiff')}
    for path in images:
        x, y = tifffile.imread(path), tifffile.imread(control / 'images' / path.name)
        assert x.dtype == y.dtype and x.shape == y.shape and np.array_equal(x, y), path
    assert len(csvs) == 6 and len(images) == 120
    parity.append({'directory': str(directory), 'label': label, 'byte_exact_csvs': [{'name': p.name, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()} for p in csvs], 'exact_label_images': len(images)})
means = {label: {key: statistics.mean(float(row[key]) for obs in observations if obs['label'] == label for row in obs['rows']) for key in ('compile_seconds', 'execute_seconds', 'total_seconds')} for label in ('main', 'candidate')} if observations else {}
report = {'parity': parity, 'means': means, 'public_observations': len(observations), 'limits': 'Complete CSV/name/label/dtype/shape/pixel equality. Public unprofiled ABBA is separate from diagnostic observations and saved-bundle replay. Thread-local timer scopes overlap; archived cProfile timing/call attribution is not valid causal evidence. CPU5, fork workers, mandatory preparation before readiness, pipeline excludes ZMQ startup/shutdown; current main source and pins. All timed runs are sequential with tests/audits/builds stopped.'}
destination = runs / ('perf-payload-slice-projection-public-comparison-20260930.json' if observations else 'perf-payload-slice-projection-diagnostic-parity-20260930.json')
destination.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'means': means, 'public_observations': len(observations), 'exact_csvs': len(parity) * 6, 'exact_labels': len(parity) * 120}))
