"""Read evidence from the original recorded MCP stdout, without copying results.

This is an offline consumer of recorded-mcp.sh, not another recorder or viewer
state owner. References address exact UTF-8 bytes and an original result ordinal.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Iterator

from python_introspect import dataclass_from_mapping

from openhcs.agent.capabilities import (
    GetViewerWindowStateCapability,
    ViewerSnapshotWindowCapability,
)
from openhcs.mcp.dev_client_core import McpDevToolResult
from openhcs.agent.dto.viewer import ViewerWindowSnapshotResult


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
            McpDevToolResult, self.response(journal)['results'][self.result_index])


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
            results = response.get('results', [])
            if not results:
                references.append(reference)
                continue
            for ordinal, raw_result in enumerate(results):
                result = dataclass_from_mapping(McpDevToolResult, raw_result)
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
        document = asdict(self)
        document['journal']['path'] = str(self.journal.path)
        return document

    @classmethod
    def read(cls, path: Path) -> RecordedMcpEvidenceIndex:
        document = json.loads(path.read_text())
        journal = document['journal']
        return cls(RecordedMcpJournal(Path(journal['path']), journal['prefix_bytes'], journal['sha256']),
                   tuple(dataclass_from_mapping(RecordedMcpResponseReference, row) for row in document['events']),
                   tuple(dataclass_from_mapping(RecordedMcpCaptureReference, row) for row in document['captures']))

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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    index = commands.add_parser('index')
    index.add_argument('--journal', type=Path, required=True)
    index.add_argument('--output', type=Path, required=True)
    verify = commands.add_parser('verify')
    verify.add_argument('--index', type=Path, required=True)
    resolve = commands.add_parser('resolve')
    resolve.add_argument('--index', type=Path, required=True)
    resolve.add_argument('--event', type=int, required=True)
    args = parser.parse_args()
    if args.command == 'index':
        evidence = RecordedMcpJournal.index(args.journal)
        evidence.verify()
        with args.output.open('x') as output:
            json.dump(evidence.to_dict(), output, indent=2)
        print(json.dumps({'events': len(evidence.events), 'captures': len(evidence.captures),
                          'indexed_prefix_bytes': evidence.journal.prefix_bytes, 'output': str(args.output)}))
    else:
        evidence = RecordedMcpEvidenceIndex.read(args.index)
        if args.command == 'verify':
            evidence.verify()
            print(json.dumps({'verified': True, 'events': len(evidence.events), 'captures': len(evidence.captures)}))
        else:
            evidence.journal.verify()
            reference = evidence.events[args.event]
            print(json.dumps(reference.response(evidence.journal)))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
