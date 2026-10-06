"""Read-only acceptance against the original frozen BBBC013 evidence indexes.

Imports the candidate reader over qualified installed owners, without editing
an installed target. Prints counts only; no repeated payload output/store.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--reader', type=Path, required=True)
parser.add_argument('--index', type=Path, required=True)
parser.add_argument('--frozen-output', type=Path, required=True)
args = parser.parse_args()
spec = importlib.util.spec_from_file_location('candidate_recorded_evidence', args.reader)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
index = module.RecordedMcpEvidenceIndex.read(args.index)
index.verify()
paths = [args.frozen_output / name for name in (
    'mcp-event-index.json', 'qa-evidence-manifest.json')]
def hashes():
    digests = []
    for path in paths:
        with path.open('rb') as source:
            digests.append(hashlib.file_digest(source, 'sha256').hexdigest())
    return digests
before = hashes()
old_events, old_captures = [json.loads(path.read_text()) for path in paths]
tool_refs = [ref for ref in index.events if ref.result_index is not None]
assert len(tool_refs) == len(old_events)
for old, ref in zip(old_events, tool_refs):
    assert ref.response(index.journal)['results'][ref.result_index] == old['result']
assert len(old_captures) == len(index.captures)
for old, capture in zip(old_captures, index.captures):
    ref = index.events[capture.event]
    result = ref.response(index.journal)['results'][ref.result_index]
    assert result['payloads'][0] == old['capture']
triad = [capture for capture in index.captures if capture.resource_path and
         '/FIRST-A01-pair-' in capture.resource_path]
assert len(triad) == 3
assert {Path(c.resource_path).parent.name.rsplit('-', 1)[-1] for c in triad} == {
    'raw', 'result', 'combined'}
for capture in triad:
    # Original states and every intervening control resolve, not copied state.
    list(index.capture_evidence(capture))
assert before == hashes()
document = json.loads(args.index.read_text())
assert all(set(row) == {'byte_offset', 'byte_length', 'sha256', 'result_index'}
           for row in document['events'])
print(json.dumps({'tool_results_exact': len(tool_refs),
                  'other_envelopes_retained': len(index.events) - len(tool_refs),
                  'capture_receipts_exact': len(index.captures),
                  'matched_raw_result_combined': len(triad),
                  'original_indexes_unchanged': True,
                  'index_bytes': args.index.stat().st_size,
                  'journal_prefix_bytes': index.journal.prefix_bytes}))
