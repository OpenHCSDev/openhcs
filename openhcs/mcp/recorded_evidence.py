"""Read evidence from the original recorded MCP stdout, without copying results.

This is an offline consumer of recorded-mcp.sh, not another recorder or viewer
state owner. References address exact UTF-8 bytes and an original result ordinal.
"""
from __future__ import annotations

import argparse
from abc import ABC, abstractmethod
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import ClassVar, Iterator, Sequence

from metaclass_registry import AutoRegisterMeta
from python_introspect import dataclass_from_mapping

from openhcs.agent.capabilities import (
    GetViewerWindowStateCapability,
    ViewerSnapshotWindowCapability,
)
from openhcs.mcp.dev_client_core import McpDevToolBatchResponse, McpDevToolResult
from openhcs.agent.dto.viewer import ViewerWindowSnapshotResult
from openhcs.serialization.json import to_jsonable


@dataclass(frozen=True)
class RecordedMcpResponseReference:
    """One original response byte span; None selects the whole envelope."""

    byte_offset: int
    byte_length: int
    sha256: str
    result_index: int | None = None

    def response(self, journal: RecordedMcpJournal) -> dict:
        if (self.byte_offset < 0 or self.byte_length <= 0
                or self.byte_offset + self.byte_length > journal.prefix_bytes):
            raise ValueError('Response reference is outside the indexed journal prefix')
        with journal.path.open('rb') as source:
            source.seek(self.byte_offset)
            original = source.read(self.byte_length)
        if hashlib.sha256(original).hexdigest() != self.sha256:
            raise ValueError('Referenced original response bytes changed')
        return json.loads(original)

    def result(self, journal: RecordedMcpJournal) -> McpDevToolResult:
        if self.result_index is None:
            raise ValueError('This reference selects an envelope, not a tool result')
        return dataclass_from_mapping(
            McpDevToolBatchResponse, self.response(journal)).results[self.result_index]


@dataclass(frozen=True)
class RecordedMcpJournal:
    """The original recorder owns bytes; this descriptor owns prefix identity."""

    path: Path
    prefix_bytes: int
    sha256: str

    def verify(self) -> None:
        digest = hashlib.sha256()
        remaining = self.prefix_bytes
        with self.path.open('rb') as source:
            while remaining:
                block = source.read(min(1024 * 1024, remaining))
                if not block:
                    raise ValueError('Original journal is shorter than the indexed prefix')
                digest.update(block)
                remaining -= len(block)
        if digest.hexdigest() != self.sha256:
            raise ValueError('Original journal prefix hash changed')

    @classmethod
    def index(cls, path: Path) -> RecordedMcpEvidenceIndex:
        original = path.read_bytes()
        journal = cls(path.absolute(), len(original), hashlib.sha256(original).hexdigest())
        text = original.decode('utf-8', errors='surrogateescape')
        decoder = json.JSONDecoder()
        references = []
        captures = []
        nearest_state = None
        char_cursor = byte_cursor = 0
        for start in re.finditer(r'(?m)^\{', text):
            if start.start() < char_cursor:
                continue
            try:
                response, end = decoder.raw_decode(text, start.start())
            except json.JSONDecodeError:
                continue
            byte_cursor += len(text[char_cursor:start.start()].encode('utf-8', errors='surrogateescape'))
            span = text[start.start():end].encode('utf-8', errors='surrogateescape')
            char_cursor = end
            reference = RecordedMcpResponseReference(
                byte_cursor, len(span), hashlib.sha256(span).hexdigest())
            byte_cursor += len(span)
            # Non-tool envelopes (including predispatch/transport errors and
            # catalog replies) stay resolvable too. Nothing is discarded from
            # the original journal, including non-JSON CLI/UNKNOWN diagnostics.
            if 'results' not in response:
                references.append(reference)
                continue
            # for_rendering uses this same whole-envelope ingress codec, then
            # projects selected DTOs. Indexing keeps original payloads instead
            # of rendering every historical capability through today's schema.
            batch = dataclass_from_mapping(McpDevToolBatchResponse, response)
            if not batch.results:
                references.append(reference)
                continue
            for ordinal, result in enumerate(batch.results):
                selected = RecordedMcpResponseReference(
                    reference.byte_offset, reference.byte_length, reference.sha256, ordinal)
                event = len(references)
                references.append(selected)
                if result.tool == GetViewerWindowStateCapability.name:
                    nearest_state = event
                elif result.tool == ViewerSnapshotWindowCapability.name:
                    # Resource identity is the only extracted capture content.
                    # The FULL snapshot and every error stay in the original.
                    payload = result.decoded_payload_as(ViewerWindowSnapshotResult)
                    resource = None if payload is None else payload.resource
                    captures.append(RecordedMcpCaptureReference(
                        event, nearest_state,
                        None if resource is None else resource.path,
                        None if resource is None else resource.sha256))
        return RecordedMcpEvidenceIndex(journal, tuple(references), tuple(captures))


@dataclass(frozen=True)
class RecordedMcpCaptureReference:
    """Capture reference and native bitmap identity, never copied viewer state."""

    event: int
    nearest_preceding_state: int | None
    resource_path: str | None
    resource_sha256: str | None

    def preceding_events(self) -> range:
        """Resolve all intervening records, not a fabricated effective state.

        The nearest full-state receipt is only historical evidence. Applied
        controls and rejection/UNKNOWN diagnostics retain their own receipts.
        """
        start = 0 if self.nearest_preceding_state is None else self.nearest_preceding_state
        return range(start, self.event)

    def verify_bitmap(self) -> None:
        if self.resource_path is None:
            return  # Failed/missing-resource snapshot still has its original event.
        with Path(self.resource_path).open('rb') as bitmap:
            actual = hashlib.file_digest(bitmap, 'sha256').hexdigest()
        if actual != self.resource_sha256:
            raise ValueError(f'Native capture hash changed: {self.resource_path}')


@dataclass(frozen=True)
class RecordedMcpEvidenceIndex:
    """References derived from one retained stdout; no result payload store."""

    journal: RecordedMcpJournal
    events: tuple[RecordedMcpResponseReference, ...]
    captures: tuple[RecordedMcpCaptureReference, ...]

    def to_dict(self) -> dict:
        return to_jsonable(self)

    @classmethod
    def read(cls, path: Path) -> RecordedMcpEvidenceIndex:
        return dataclass_from_mapping(cls, json.loads(path.read_text()))

    def capture_evidence(self, capture: RecordedMcpCaptureReference) -> Iterator[dict]:
        self.journal.verify()
        for event in (*capture.preceding_events(), capture.event):
            reference = self.events[event]
            yield reference.response(self.journal)

    def verify(self) -> None:
        self.journal.verify()
        for reference in self.events:
            reference.response(self.journal)
        for capture in self.captures:
            capture.verify_bitmap()


class RecordedEvidenceCommand(ABC, metaclass=AutoRegisterMeta):
    """Offline commands, declared and dispatched like BenchmarkCliCommand."""

    __registry_key__ = 'command_name'
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[RecordedEvidenceCommand]]] = {}
    command_name: ClassVar[str | None] = None
    help_text: ClassVar[str]

    @classmethod
    def registered_commands(cls) -> tuple[RecordedEvidenceCommand, ...]:
        return tuple(command_type() for command_type in cls.__registry__.values())

    def configure(self, subparsers: argparse._SubParsersAction) -> argparse.ArgumentParser:
        parser = subparsers.add_parser(self.command_name, help=self.help_text)
        parser.set_defaults(cli_command=self)
        self.configure_arguments(parser)
        return parser

    @abstractmethod
    def configure_arguments(self, parser: argparse.ArgumentParser) -> None:
        """Declare arguments owned by this operation."""

    @abstractmethod
    def run(self, args: argparse.Namespace) -> int:
        """Perform this offline operation without a command-name switch."""


class IndexRecordedEvidenceCommand(RecordedEvidenceCommand):
    command_name = 'index'
    help_text = 'Index original recorded response bytes without copying payloads.'

    def configure_arguments(self, parser: argparse.ArgumentParser) -> None:
        parser.add_argument('--journal', type=Path, required=True)
        parser.add_argument('--output', type=Path, required=True)

    def run(self, args: argparse.Namespace) -> int:
        evidence = RecordedMcpJournal.index(args.journal)
        evidence.verify()
        with args.output.open('x') as output:
            json.dump(to_jsonable(evidence), output, indent=2)
        print(json.dumps({'events': len(evidence.events), 'captures': len(evidence.captures),
                          'indexed_prefix_bytes': evidence.journal.prefix_bytes, 'output': str(args.output)}))
        return 0


class IndexedRecordedEvidenceCommand(RecordedEvidenceCommand):
    """Shared declared index input for operations consuming retained references."""

    def configure_arguments(self, parser: argparse.ArgumentParser) -> None:
        parser.add_argument('--index', type=Path, required=True)


class VerifyRecordedEvidenceCommand(IndexedRecordedEvidenceCommand):
    command_name = 'verify'
    help_text = 'Verify the indexed prefix, original response bytes and capture hashes.'

    def run(self, args: argparse.Namespace) -> int:
        evidence = RecordedMcpEvidenceIndex.read(args.index)
        evidence.verify()
        print(json.dumps({'verified': True, 'events': len(evidence.events), 'captures': len(evidence.captures)}))
        return 0


class ResolveRecordedEvidenceCommand(IndexedRecordedEvidenceCommand):
    command_name = 'resolve'
    help_text = 'Read an exact original response envelope by indexed event.'

    def configure_arguments(self, parser: argparse.ArgumentParser) -> None:
        super().configure_arguments(parser)
        parser.add_argument('--event', type=int, required=True)

    def run(self, args: argparse.Namespace) -> int:
        evidence = RecordedMcpEvidenceIndex.read(args.index)
        evidence.journal.verify()
        reference = evidence.events[args.event]
        print(json.dumps(reference.response(evidence.journal)))
        return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(required=True)
    for command in RecordedEvidenceCommand.registered_commands():
        command.configure(commands)
    args = parser.parse_args(argv)
    return args.cli_command.run(args)


if __name__ == '__main__':
    raise SystemExit(main())
