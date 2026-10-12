"""The run request names an export scope; the session receives the scope class."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from openhcs.agent.dto.session import (
    DatasetRunRequest,
    RuntimeObservationExportScopeName,
)
from openhcs.authoring.session.operations.datasets import RunDatasets
from openhcs.authoring.session.session import Session
from openhcs.runtime.zmq_execution_signature import ZMQRuntimeObservationExportScope

SCOPE_NAMES = tuple(ZMQRuntimeObservationExportScope.__registry__)


class _WritableAnywhere:
    @staticmethod
    def require_writable(path: Path) -> Path:
        return path


class _RecordingSession:
    """Only what ``RunDatasets.run`` touches; the export options are the real ones."""

    observation_export_params = Session.observation_export_params
    dataset_access = _WritableAnywhere()
    event_log = SimpleNamespace(last_sequence=0)
    run_datasets = object()

    def start(self, work, scope_ids, **options) -> None:
        self.started = (work, scope_ids, options)


def test_every_registered_scope_has_a_request_name() -> None:
    assert {member.value for member in RuntimeObservationExportScopeName} == set(
        SCOPE_NAMES
    )


@pytest.mark.parametrize("scope_name", SCOPE_NAMES)
def test_run_datasets_gives_the_session_the_scope_class(
    scope_name: str, tmp_path: Path
) -> None:
    session = _RecordingSession()
    export_path = tmp_path / "observation.pkl"

    result = RunDatasets.run(
        session,
        DatasetRunRequest(
            scope_ids=("dataset",),
            runtime_observation_export_path=str(export_path),
            runtime_observation_export_scope=RuntimeObservationExportScopeName(
                scope_name
            ),
        ),
    )

    work, scope_ids, options = session.started
    assert result.status == "accepted"
    assert work is session.run_datasets
    assert scope_ids == ("dataset",)
    export = options["auxiliary_params"]
    assert export.runtime_observation_export_path == export_path
    assert export.runtime_observation_export_scope is (
        ZMQRuntimeObservationExportScope.named(scope_name)
    )


def test_run_datasets_without_an_export_path_runs_with_the_default_scope() -> None:
    session = _RecordingSession()

    RunDatasets.run(session, DatasetRunRequest(scope_ids=("dataset",)))

    assert session.started[2]["auxiliary_params"] is None


def test_run_request_refuses_the_scope_class_itself() -> None:
    with pytest.raises(TypeError, match="runtime_observation_export_scope"):
        DatasetRunRequest(
            scope_ids=(),
            runtime_observation_export_scope=ZMQRuntimeObservationExportScope.named(
                SCOPE_NAMES[0]
            ),
        )
