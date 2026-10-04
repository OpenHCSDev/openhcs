"""Use the original source bootstrap and pytest; no native/catalog initialization."""

import hashlib
import json
from pathlib import Path
import sys

owned = Path(__file__).resolve().parents[2]
root = Path('/home/ts/wt/openhcs-issue-batch-20260929/engineering599')
source = owned
diagnostic = '--original-diagnostic' in sys.argv
if diagnostic:
    source = root / 'original-main'
    sys.argv.remove('--original-diagnostic')
sys.path.insert(0, '/home/ts/code/projects/openhcs/.venv/lib/python3.12/site-packages')
sys.path.insert(0, str(source))
import openhcs
from openhcs._source_dependencies import ensure_source_checkout_external_paths
ensure_source_checkout_external_paths(root / 'source-runtime')

import numpy as np
import openhcs.core.runtime_image_values as values
from openhcs.core.aligned_image_payload import stack_image_payloads
assert Path(values.__file__).is_relative_to(source)
print(json.dumps({'source': str(source), 'metadata_module': values.__file__,
    'sha256': hashlib.sha256(Path(values.__file__).read_bytes()).hexdigest(),
    'mode': 'original source; no viewer/server/catalog/installed acceptance'}), flush=True)

if diagnostic:
    scalar = np.full((2, 3), 128, dtype=np.uint8)
    raw = values.ImagePayloadMetadata.for_array(scalar).payload_with(scalar)
    normalized = values.normalize_image_payload_intensity(raw)
    rgb_mono = values.ImagePayloadMetadata(
        source_dtype='uint8',
        unit_interval_intensity=values.ImageUnitIntervalIntensityMetadata(),
    ).payload_with(np.full((2, 3), 128 / 255, dtype=np.float32))
    mixed = stack_image_payloads((raw, rgb_mono),
        metadata_mode=values.ImagePayloadMetadataCompositionMode.BUNDLE)
    selected = values.image_payload_metadata(mixed).for_leading_source_plane(0).payload_with(
        values.image_payload_data(mixed)[0])
    actual = values.normalize_image_payload_intensity(selected)
    print(json.dumps({'independent': np.asarray(normalized).tolist(),
        'mixed_then_selected': np.asarray(actual).tolist(),
        'mixed_dtype': str(np.asarray(mixed).dtype),
        'equivalent': bool(np.allclose(actual, normalized))}), flush=True)
    raise SystemExit(0)

import pytest
raise SystemExit(pytest.main(['--noconftest', '--import-mode=importlib',
    '-p', 'no:cacheprovider', '-o', 'addopts=', '-q', *sys.argv[1:]]))
