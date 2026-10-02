"""Real terminal boundary; original CLI/parser with controlled transport only."""

from __future__ import annotations

import hashlib
import io
import json
import os
import pty
import select
import shlex
import subprocess
import sys
import termios
import time

import pytest


CHILD = r'''
import fcntl, hashlib, json, os, sys, termios
from contextlib import contextmanager
fcntl.ioctl(0, termios.TIOCSCTTY, 0)
import openhcs.mcp.dev_client as cli

class ControlledClient:
    def __init__(self, *args, **kwargs):
        @contextmanager
        def source_context():
            with kwargs['stdin_context']():
                print("SOURCE_INPUT_READY", flush=True)
                yield
        self.stdin_context = source_context
    def __enter__(self):
        print("INITIALIZING", flush=True)
        os.read(int(sys.argv[1]), 1)
        if sys.argv[2] == "fail-start":
            raise RuntimeError("controlled initialization failure")
        return self
    def __exit__(self, *args):
        print("CLIENT_CLOSED", flush=True)
    def execute(self, argv):
        args = cli._build_parser().parse_args(argv)
        spec = cli.McpDevCommandSpec.for_name(args.command)
        spec.prepare_input(args, stdin_context=self.stdin_context)
        calls = spec.calls_from_args(args)
        for call in calls:
            body = json.dumps(call.arguments, ensure_ascii=False, sort_keys=True).encode()
            print("ADMITTED:" + call.name + ":" + hashlib.sha256(body).hexdigest(), flush=True)
        return cli.McpDevCommandExecution(tuple(argv), {}, "CONTROLLED_RESULT", 0, None)

cli.McpDevClient = ControlledClient
raise SystemExit(cli.main(["--timeout-seconds", "10", "shell", "--no-prompt"]))
'''


def _pump(master: int, send: bytes = b"", *, until: bytes) -> bytes:
    """Drive only this retained test child/PTY, with a bounded observation."""
    output = bytearray()
    deadline = time.monotonic() + 15
    while send or until not in output:
        remaining = deadline - time.monotonic()
        assert remaining > 0, bytes(output)[-1000:]
        readable, writable, _ = select.select(
            [master], [master] if send else [], [], remaining
        )
        if writable:
            send = send[os.write(master, send):]
        if readable:
            try:
                chunk = os.read(master, 65536)
            except OSError:
                break
            if not chunk:
                break
            output.extend(chunk)
    assert until in output, bytes(output)[-1000:]
    return bytes(output)


@pytest.fixture
def terminal_child():
    children = []

    def start(mode="normal"):
        master, slave = pty.openpty()
        os.set_blocking(master, False)
        original = termios.tcgetattr(slave)
        admission_read, admission_write = os.pipe()
        child = subprocess.Popen(
            [sys.executable, "-B", "-c", CHILD, str(admission_read), mode],
            stdin=slave, stdout=slave, stderr=slave,
            pass_fds=(admission_read,), start_new_session=True,
        )
        os.close(admission_read)
        children.append((child, master, slave, admission_write))
        _pump(master, until=b"INITIALIZING")
        assert not termios.tcgetattr(slave)[3] & termios.ICANON
        return child, master, slave, admission_write, original

    yield start
    for child, master, slave, admission_write in children:
        if child.poll() is None:
            child.terminate()
            child.wait(timeout=5)
        for descriptor in (master, slave, admission_write):
            os.close(descriptor)


@pytest.mark.parametrize("text", ["'quoted\\source'" * 600, "µ😀" * 5000])
def test_long_terminal_command_reuses_original_parser_and_client(terminal_child, text):
    child, master, slave, release, original = terminal_child()
    arguments = {"independent_payload": text}
    serialized = json.dumps(arguments, ensure_ascii=False)
    digest = hashlib.sha256(
        json.dumps(arguments, ensure_ascii=False, sort_keys=True).encode()
    ).hexdigest()
    command = "call independent_external_probe --arguments " + shlex.quote(serialized)
    assert len(command.encode()) > 4096
    os.write(release, b"1")
    output = _pump(
        master, (command + "\nhealth\nquit\n").encode(), until=b"CLIENT_CLOSED"
    )
    assert output.count(("ADMITTED:independent_external_probe:" + digest).encode()) == 1
    assert output.count(b"ADMITTED:openhcs_health_check:") == 1
    assert child.wait(timeout=5) == 0
    assert termios.tcgetattr(slave) == original


def test_command_queued_during_initialization_is_not_truncated(terminal_child):
    child, master, slave, release, original = terminal_child()
    arguments = {"document": "a" * 5200}
    serialized = json.dumps(arguments)
    command = "call independent_queued_probe --arguments " + shlex.quote(serialized)
    queued = (command + "\nquit\n").encode()
    sent = os.write(master, queued)
    os.write(release, b"1")
    output = _pump(master, queued[sent:], until=b"CLIENT_CLOSED")
    digest = hashlib.sha256(json.dumps(arguments, sort_keys=True).encode()).hexdigest()
    assert ("ADMITTED:independent_queued_probe:" + digest).encode() in output
    assert child.wait(timeout=5) == 0
    assert termios.tcgetattr(slave) == original


def test_terminal_keeps_quote_errors_and_next_command(terminal_child):
    child, master, slave, release, original = terminal_child()
    os.write(release, b"1")
    output = _pump(master, b"call probe --arguments '\nhealth\nquit\n", until=b"CLIENT_CLOSED")
    assert b"error: No closing quotation" in output
    assert b"ADMITTED:probe:" not in output
    assert output.count(b"ADMITTED:openhcs_health_check:") == 1
    assert child.wait(timeout=5) == 2
    assert termios.tcgetattr(slave) == original


def test_terminal_editor_preserves_erase_and_eof(terminal_child):
    child, master, slave, release, original = terminal_child()
    os.write(release, b"1")
    output = _pump(master, b"healthZ\x7f\n\x04", until=b"CLIENT_CLOSED")
    assert output.count(b"ADMITTED:openhcs_health_check:") == 1
    assert child.wait(timeout=5) == 0
    assert termios.tcgetattr(slave) == original


def test_terminal_mode_restored_after_initialization_failure(terminal_child):
    child, master, slave, release, original = terminal_child("fail-start")
    os.write(release, b"1")
    output = _pump(master, until=b"controlled initialization failure")
    assert b"ADMITTED:" not in output
    assert child.wait(timeout=5) == 1
    assert termios.tcgetattr(slave) == original


def test_blank_line_keeps_terminal_session_alive(terminal_child):
    child, master, slave, release, original = terminal_child()
    os.write(release, b"1")
    output = _pump(master, b"\n# ignored\nhealth\nquit\n", until=b"CLIENT_CLOSED")
    assert output.count(b"ADMITTED:openhcs_health_check:") == 1
    assert child.wait(timeout=5) == 0
    assert termios.tcgetattr(slave) == original


def test_terminal_stdin_source_keeps_exact_eof_bytes_and_reuses_shell(terminal_child):
    child, master, slave, release, original = terminal_child()
    os.write(release, b"1")
    _pump(
        master, b"artifact-plan /not-opened --source-file -\n",
        until=b"SOURCE_INPUT_READY",
    )
    assert termios.tcgetattr(slave) == original
    source = "# original source\npipeline_steps = []"
    arguments = {
        "plate_path": "/not-opened",
        "pipeline_source": source,
        "axis_filter": None,
        "global_config_id": None,
    }
    digest = hashlib.sha256(
        json.dumps(arguments, ensure_ascii=False, sort_keys=True).encode()
    ).hexdigest().encode()
    _pump(master, source.encode() + b"\x04\x04", until=digest)
    assert not termios.tcgetattr(slave)[3] & termios.ICANON
    output = _pump(master, b"health\nquit\n", until=b"CLIENT_CLOSED")
    assert output.count(b"ADMITTED:openhcs_health_check:") == 1
    assert child.wait(timeout=5) == 0
    assert termios.tcgetattr(slave) == original


def test_independent_source_declaration_composes_cooperative_preparation(monkeypatch):
    from openhcs.mcp import dev_client as cli
    from openhcs.mcp.dev_client_commanding import McpDevCommandSpec, StdinSourceCommandSpec
    from openhcs.mcp.dev_client_core import (
        McpDevToolCall,
        add_pipeline_source_options,
        pipeline_source_from_args,
    )

    events = []

    class IndependentPreparation(McpDevCommandSpec):
        def prepare_input(self, args, *, stdin_context=cli.nullcontext):
            events.append(("before", args.source_file))
            super().prepare_input(args, stdin_context=stdin_context)
            events.append(("after", args.source_file))

    class IndependentSource(
        StdinSourceCommandSpec, IndependentPreparation, McpDevCommandSpec
    ):
        command = "independent-stdin-source-proof"

        def configure_parser(self, parser):
            add_pipeline_source_options(parser)

        def calls_from_args(self, args):
            return (McpDevToolCall(
                "independent_external_source",
                {"source": pipeline_source_from_args(args)},
            ),)

    source = "# exact independent source\nµ = 'unchanged'"
    monkeypatch.setattr(sys, "stdin", io.StringIO(source))
    try:
        args = cli._build_parser().parse_args([
            IndependentSource.command, "--source-file", "-",
        ])
        # Original generic ingress discovers the new declaration and composes
        # both hooks without a consumer edit or a parallel command roster.
        calls = cli._calls_from_args(args)
        assert calls[0].arguments == {"source": source}
        assert events == [("before", "-"), ("after", "-")]
        assert args.source_file is None
        assert args.source_text == source
        assert sys.stdin.read() == ""
    finally:
        McpDevCommandSpec.__registry__.pop(IndependentSource.command)
