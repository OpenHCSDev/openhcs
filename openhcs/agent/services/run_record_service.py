"""Read the record of what produced an output dataset, for agents."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path

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


def _entry(record: RunRecord, request: RunRecordReadRequest) -> RunRecordEntry:
    """What each step ran, with the complete stored record when the request asks for it."""
    return RunRecordEntry(
        record_id=record.record_id,
        steps=tuple(step.calls for step in record.steps),
        record=record if request.include_full_record else None,
    )


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
    def read(self, request: RunRecordReadRequest) -> RunRecordReadResult:
        """Read this target with the detail the request asks for."""


class DatasetRootTarget(RunRecordTarget):
    def read(self, request: RunRecordReadRequest) -> RunRecordReadResult:
        return RunRecordReadResult(
            schema_version=SCHEMA_VERSION,
            path=str(self.path),
            records=tuple(
                _entry(record, request)
                for record in RunRecord.for_dataset(self.path).values()
            ),
        )


class OutputFileTarget(RunRecordTarget):
    def read(self, request: RunRecordReadRequest) -> RunRecordReadResult:
        try:
            produced = RunRecord.for_output_file(self.path)
        except UnrecordedOutputFile as error:
            raise OutputFileNotRecorded(str(error), path=str(self.path)) from error
        return RunRecordReadResult(
            schema_version=SCHEMA_VERSION,
            path=str(self.path),
            records=(_entry(produced.record, request),),
            produced_files=(
                ProducedFileEntry(
                    path=str(self.path),
                    record_id=produced.record.record_id,
                    producer=produced.producer,
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
        return target.read(request)
