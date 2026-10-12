"""Read the record of what produced an output dataset, for agents."""

from __future__ import annotations

import hashlib
import json
from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path

from python_introspect import JsonObject

from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.plate import (
    ProducedFileEntry,
    RunRecordEntry,
    RunRecordReadRequest,
    RunRecordReadResult,
)
from openhcs.agent.exceptions import AgentFacingErrorMixin
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.core.run_record import RunRecord, UnrecordedOutputFile
from openhcs.core.virtual_workspace_metadata import get_metadata_path


class OutputFileNotRecorded(AgentFacingErrorMixin, LookupError):
    """The dataset's metadata does not say which step produced the requested file."""

    agent_error_code = "run_record_output_file_unrecorded"
    agent_error_hint = (
        "Pass the output dataset root to list its run records, or a file the "
        "dataset's metadata lists under produced_files."
    )


def _digest(text: str) -> JsonObject:
    return {
        "shortened": True,
        "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
        "length": len(text),
    }


def _shortened(record: RunRecord) -> RunRecordEntry:
    """The record with each long text replaced by its sha256 and length.

    ``installed_distributions`` is digested as its sorted compact JSON text.
    """
    content = record.content
    software = content["software"]
    custom_sources = content["custom_sources"]
    return RunRecordEntry(
        record_id=record.record_id,
        record={
            **content,
            "software": {
                **software,
                "installed_distributions": _digest(
                    json.dumps(
                        software["installed_distributions"],
                        sort_keys=True,
                        separators=(",", ":"),
                    )
                ),
            },
            "pipeline_code": _digest(content["pipeline_code"]),
            "global_config_code": _digest(content["global_config_code"]),
            "custom_sources": {
                source_sha256: _digest(text)
                for source_sha256, text in custom_sources.items()
            },
        },
        shortened_fields=(
            "software.installed_distributions",
            "pipeline_code",
            "global_config_code",
            *(f"custom_sources.{source_sha256}" for source_sha256 in custom_sources),
        ),
    )


def _in_full(record: RunRecord) -> RunRecordEntry:
    return RunRecordEntry(record_id=record.record_id, record=dict(record.content))


@dataclass(frozen=True, slots=True)
class RunRecordTarget(ABC):
    """A readable path a run record is asked for: a dataset root or a file inside one."""

    path: Path

    @classmethod
    def at(cls, path: Path) -> "RunRecordTarget":
        """A directory holding the metadata document is a dataset root; anything else is a file."""
        if Path(get_metadata_path(path)).is_file():
            return DatasetRootTarget(path)
        return OutputFileTarget(path)

    @abstractmethod
    def read(self, request: RunRecordReadRequest, entry) -> RunRecordReadResult:
        """Read this target; ``entry`` turns a ``RunRecord`` into its returned form."""


class DatasetRootTarget(RunRecordTarget):
    def read(self, request: RunRecordReadRequest, entry) -> RunRecordReadResult:
        return RunRecordReadResult(
            schema_version=SCHEMA_VERSION,
            path=str(self.path),
            include_sources=request.include_sources,
            records=tuple(
                entry(record) for record in RunRecord.for_dataset(self.path).values()
            ),
        )


class OutputFileTarget(RunRecordTarget):
    def read(self, request: RunRecordReadRequest, entry) -> RunRecordReadResult:
        try:
            produced = RunRecord.for_output_file(self.path)
        except UnrecordedOutputFile as error:
            raise OutputFileNotRecorded(str(error), path=str(self.path)) from error
        return RunRecordReadResult(
            schema_version=SCHEMA_VERSION,
            path=str(self.path),
            include_sources=request.include_sources,
            records=(entry(produced.record),),
            produced_files=(
                ProducedFileEntry(
                    path=str(self.path),
                    record_id=produced.record.record_id,
                    producer=dict(produced.producer.to_payload()),
                    step=produced.step,
                ),
            ),
        )


class RunRecordService:
    """Wrap ``RunRecord``'s readers behind the agent path policy."""

    def __init__(self, path_policy: AgentPathPolicy) -> None:
        self._path_policy = path_policy

    def read(self, request: RunRecordReadRequest) -> RunRecordReadResult:
        target = RunRecordTarget.at(self._path_policy.assert_readable(request.path))
        return target.read(request, _in_full if request.include_sources else _shortened)
