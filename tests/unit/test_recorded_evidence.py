import json
from pathlib import Path

import pytest

from openhcs.agent.capabilities import ViewerSnapshotWindowCapability
from openhcs.mcp.recorded_evidence import (
    RecordedEvidenceCommand, RecordedMcpJournal, RecordedMcpEvidenceIndex, main,
)


def journal(tmp_path, results):
    path = tmp_path / 'mcp.stdout'
    envelope = {'server': {'command': 'retained-python', 'module': 'openhcs.mcp'},
                'results': results, 'errors': []}
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


def test_non_tool_envelope_is_resolvable(tmp_path):
    path = tmp_path / 'mcp.stdout'
    envelope = {'catalog': ['retained'], 'diagnostic': 'UNKNOWN'}
    path.write_text(json.dumps(envelope, indent=2) + '\nuntouched CLI error')
    index = RecordedMcpJournal.index(path)
    index.verify()
    assert index.events[0].result_index is None
    assert index.events[0].response(index.journal) == envelope


def test_whole_index_codec_owns_nested_path_and_rejects_extra_field(tmp_path):
    path, _ = journal(tmp_path, [])
    index = RecordedMcpJournal.index(path)
    serialized = tmp_path / 'index.json'
    document = index.to_dict()
    serialized.write_text(json.dumps(document))
    assert isinstance(RecordedMcpEvidenceIndex.read(serialized).journal.path, Path)
    document['journal']['extra'] = 'undeclared'
    serialized.write_text(json.dumps(document))
    with pytest.raises(ValueError, match='undeclared'):
        RecordedMcpEvidenceIndex.read(serialized)


def test_registered_command_behavior_drives_parser_and_dispatch():
    observed = []

    class WitnessCommand(RecordedEvidenceCommand):
        command_name = 'registration-witness'
        help_text = 'Test registration without editing a parser roster.'

        def configure_arguments(self, parser):
            parser.add_argument('--value', required=True)

        def run(self, args):
            observed.append(args.value)
            return 17

    try:
        assert main(['registration-witness', '--value', 'owned']) == 17
        assert observed == ['owned']
    finally:
        RecordedEvidenceCommand.__registry__.pop(WitnessCommand.command_name)
