import argparse
import hashlib
import json
import pickle
import statistics
import time
from pathlib import Path

import numpy as np
from openhcs.core import runtime_image_values as values

parser = argparse.ArgumentParser()
parser.add_argument('--label', required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
runs = Path('/home/ts/code/projects/openhcs-benchmark-runs')
fixtures = runs / 'perf-source-header-current-runtime-profile-20260930'
rows = []
for step in (1, 13, 17):
    path = next(fixtures.glob(f'step-{step}-*_validate_and_unstack.pickle'))
    blob = path.read_bytes(); fixture = pickle.loads(blob)
    saved = fixture['output_data']
    actual = tuple(fixture['processed_stack'].projected_output_slices())
    assert len(actual) == len(saved.slices) == 60
    assert tuple(context for _, context in actual) == saved.slice_contexts
    for (payload, _context), expected in zip(actual, saved.slices, strict=True):
        assert type(payload) is type(expected)
        assert values.image_payload_metadata(payload) == values.image_payload_metadata(expected)
        x, y = values.image_payload_data(payload), values.image_payload_data(expected)
        assert x.dtype == y.dtype
        np.testing.assert_array_equal(x, y)
        x, y = values.image_payload_mask(payload), values.image_payload_mask(expected)
        if x is None:
            assert y is None
        else:
            assert x.dtype == y.dtype
            np.testing.assert_array_equal(x, y)
    samples = []
    for _ in range(11):
        started = time.perf_counter()
        tuple(fixture['processed_stack'].projected_output_slices())
        samples.append(time.perf_counter() - started)
    rows.append({'step': step, 'fixture': str(path), 'fixture_sha256': hashlib.sha256(blob).hexdigest(), 'exact_parity': True, 'samples': samples, 'median': statistics.median(samples)})
args.output.write_text(json.dumps({'label': args.label, 'runtime_module': values.__file__, 'rows': rows, 'limits': 'Sequential unprofiled saved real bundles. Includes projection, no other tests/audits/builds/benchmarks overlap. Microreplay only, not whole-runtime evidence.'}, indent=2) + '\n')
print(json.dumps({'label': args.label, 'rows': [{'step': row['step'], 'median': row['median']} for row in rows]}))
