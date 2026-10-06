import json
from pathlib import Path

import pytest

from openhcs.agent.capabilities import ViewerSnapshotWindowCapability
from openhcs.mcp.recorded_evidence import RecordedMcpJournal, RecordedMcpEvidenceIndex


def journal(tmp_path, results):
    path = tmp_path / 'mcp.stdout'
    envelope = {'results': results, 'errors': []}
    path.write_bytes(('UNKNOWN retained — α\r\n' + json.dumps(envelope, indent=2,
                      ensure_ascii=False) + '\r\nfooter').encode())
    return path, envelope


def test_exact_bytes_multiple_results_and_round_trip(tmp_path):
    path, envelope = journal(tmp_path, [
        {'tool': 'one', 'mcp_error': False, 'payloads': [{'nested': {'value': 'λ'}}]},
        {'tool': 'two', 'mcp_error': True, 'payloads': [{'error': 'UNKNOWN'}]},
    ])
    index = RecordedMcpJournal.index(path)
    index.verify()
    assert len(index.events) == 2
    assert index.events[0].response(index.journal) == envelope
    assert index.events[1].result(index.journal).mcp_error
    destination = tmp_path / 'index.json'
    destination.write_text(json.dumps(index.to_dict()))
    restored = RecordedMcpEvidenceIndex.read(destination)
    assert restored == index
    assert 'nested' not in destination.read_text()
    assert 'UNKNOWN retained' in path.read_text()


def test_append_only_is_not_frozen_whole_file(tmp_path):
    path, _ = journal(tmp_path, [])
    index = RecordedMcpJournal.index(path)
    with path.open('ab') as writer:
        writer.write(b'\nlate footer')
    index.verify()
    assert path.stat().st_size > index.journal.prefix_bytes


@pytest.mark.parametrize('changed', [b'', b'x' * 400])
def test_original_truncation_or_mutation_rejected(tmp_path, changed):
    path, _ = journal(tmp_path, [])
    index = RecordedMcpJournal.index(path)
    path.write_bytes(changed)
    with pytest.raises(ValueError):
        index.verify()


def test_failed_snapshot_keeps_event_not_fake_resource(tmp_path):
    path, _ = journal(tmp_path, [{'tool': ViewerSnapshotWindowCapability.name,
                                 'mcp_error': True, 'payloads': []}])
    index = RecordedMcpJournal.index(path)
    index.verify()
    assert len(index.captures) == 1
    assert index.captures[0].resource_path is None
    assert index.events[0].result(index.journal).mcp_error
