"""Receive closed engineering replies offline through the original CLI.

Only the wire peer is controlled; never reconnect to or replay a native mutation.
"""
from contextlib import asynccontextmanager
from io import StringIO
import json
from pathlib import Path
import shlex

import pytest

from test_mcp_dev_client_pipeline_results import ControlledWireSession
from openhcs.agent.dto.functions import CustomFunctionRegistrationObservation
from openhcs.mcp import dev_client
from openhcs.mcp.dev_client_core import McpDevPayloadFailure, McpDevToolBatchResponse
from openhcs.serialization.json import to_jsonable


ROOT = Path('/home/ts/wt/openhcs-issue-batch-20260929/engineering567/public94-attempt01')


@pytest.mark.parametrize('mutation,message', (
    (None, None),
    ({'outcome': 'not_observed'}, 'disagrees with its constructed value'),
    ({'outcome': True}, 'must be one of'),
    ({'extra': 'not declared'}, 'undeclared field'),
))
def test_saved_native_success_and_declared_contradictions_through_normal_shell(
    monkeypatch, capsys, mutation, message,
):
    receipts = json.loads((ROOT / 'PUBLIC-REPLIES-FINAL01.json').read_text())
    original_lines = (ROOT / 'ADMIN_REGISTRATION56794/author-workspace/output/runtime/mcp.stdin').read_text().splitlines()
    commands = tuple(line for line in original_lines if line.startswith('call '))
    assert len(commands) == len(receipts) == 8
    assert tuple(shlex.split(line)[1] for line in commands) == tuple(row['tool'] for row in receipts)
    status_index = next(index for index, row in enumerate(receipts)
                        if row['tool'] == 'openhcs_get_custom_function_registration_status')
    original_status = json.loads(json.dumps(receipts[status_index]['payloads'][0]))
    if mutation is not None:
        commands = (commands[status_index],)
        receipts = [receipts[status_index]]
        receipts[0]['payloads'][0].update(mutation)
    peer = ControlledWireSession(tuple(row['payloads'][0] for row in receipts))

    @asynccontextmanager
    async def closed_wire_peer(*args, **kwargs):
        yield peer

    def forbidden_launch(*args, **kwargs):
        raise AssertionError('Closed-reply acceptance must never launch a process')

    import asyncio
    import subprocess
    monkeypatch.setattr(asyncio, 'create_subprocess_exec', forbidden_launch)
    monkeypatch.setattr(asyncio, 'create_subprocess_shell', forbidden_launch)
    monkeypatch.setattr(subprocess, 'Popen', forbidden_launch)
    monkeypatch.setattr(dev_client, 'open_mcp_dev_session', closed_wire_peer)
    monkeypatch.setattr('sys.stdin', StringIO('\n'.join((*commands, 'exit', ''))))
    # main -> persistent shell -> original client lifecycle/execute -> actual
    # command/session/framing/DTO codec -> canonical JSON -> shell returncode.
    terminal = dev_client.main(['shell', '--no-resident', '--no-prompt'])
    output = capsys.readouterr()
    assert not output.err
    batches = []
    remaining = output.out.lstrip()
    decoder = json.JSONDecoder()
    while remaining:
        batch, end = decoder.raw_decode(remaining)
        batches.append(batch)
        remaining = remaining[end:].lstrip()
    assert len(batches) == len(commands)
    assert tuple(call[0] for call in peer.calls) == tuple(row['tool'] for row in receipts)
    for command, call in zip(commands, peer.calls):
        arguments = shlex.split(command)
        assert call[1] == json.loads(arguments[arguments.index('--arguments') + 1])
    if mutation is None:
        assert terminal == 0
        for batch in batches:
            restored = McpDevToolBatchResponse.for_rendering(batch)
            assert not restored.has_errors()
            assert not restored.diagnostic_errors()
        restored_status = McpDevToolBatchResponse.for_rendering(batches[status_index])
        value = restored_status.results[0].first_decoded_payload()
        assert isinstance(value, CustomFunctionRegistrationObservation)
        assert to_jsonable(value) == original_status
        assert value.outcome.value == 'registered'
        assert len(value.published_sources) == 1
        assert value.persisted_source is not None
    else:
        assert terminal == 1
        rejection = batches[0]['results'][0]['payloads'][0]
        assert rejection['receipt'] == {**original_status, **mutation}
        assert rejection['receipt']['errors'] == []
        assert len(rejection['errors']) == 1
        cause = rejection['errors'][0]
        assert cause['code'] == 'mcp_payload_invalid'
        assert cause['exception_type'] == 'ValueError'
        assert message in cause['message']
        restored = McpDevToolBatchResponse.for_rendering(batches[0])
        assert restored.has_errors()
        assert isinstance(restored.results[0].payloads[0], McpDevPayloadFailure)
        assert to_jsonable(restored.diagnostic_errors()) == rejection['errors']
    # Preserve full canonical user output and actual exit, not only assertions.
    print(json.dumps({'case': mutation, 'terminal': terminal,
                      'controlled_wire_calls': len(peer.calls)}))
    print(output.out, end='')
