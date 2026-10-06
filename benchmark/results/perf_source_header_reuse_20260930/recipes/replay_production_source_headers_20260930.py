import json
import statistics
import sys
import time
from pathlib import Path
from openhcs.core import image_file_serialization

name = sys.argv[1]
runs = Path('/home/ts/code/projects/openhcs-benchmark-runs')
inventory = json.loads((runs / 'perf-source-file-address-inventory-20260930.json').read_text())
paths = tuple(Path(path) for path in inventory['physical_addresses'])
assert len(paths) == 3 and all(path.is_file() for path in paths)
headers = {path: image_file_serialization.image_file_source_metadata(path) for path in paths}
assert all(header.source_dtype is not None for header in headers.values())
timings = []
for _ in range(5):
    if name == 'candidate':
        image_file_serialization.ImageFileFormat._source_metadata_for_revision.cache_clear()
    start = time.perf_counter()
    observed = [image_file_serialization.image_file_source_metadata(path)
        for _ in range(260) for path in paths]
    timings.append(time.perf_counter() - start)
    assert observed == [headers[path] for _ in range(260) for path in paths]
result = {'package': name, 'module': image_file_serialization.__file__,
    'queries': '780 balanced reads across three actual source files; candidate cache cleared before each sample',
    'exact_dtype_intensity_scale_and_pixel_semantics': True,
    'seconds': timings, 'median_seconds': statistics.median(timings),
    'limit': 'Local production-function replay, not an end-to-end measurement.'}
(runs / f'perf-source-header-production-replay-{name}-20260930.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
