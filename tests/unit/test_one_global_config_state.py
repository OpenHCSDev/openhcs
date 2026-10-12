"""A session has one state holding the global config, from its start to its end.

Nothing a session does on the way (adding, initialising, compiling or running a
dataset) writes the global config, so an unsaved edit of it stays unsaved until
the user saves it or the config is replaced with ``apply_global_config``.
"""

from __future__ import annotations

import asyncio
import threading
from pathlib import Path

from objectstate import (
    ObjectState,
    ObjectStateRegistry,
    get_live_global_config,
    get_saved_global_config,
)

from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.authoring.session import compile_batch as compile_batch_module
from openhcs.constants.constants import OrchestratorReady
from openhcs.core.artifact_inspection import CompiledArtifactInspection
from openhcs.core.config import GlobalPipelineConfig
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.runtime.zmq_config import OpenHCSZMQConfig
from tests.unit.pyqt_gui.session_harness import (
    add_datasets,
    caller_session,
    session_gui,
    session_port,
)

SAVED_WORKERS = 2
EDITED_WORKERS = 11


def _global_state() -> ObjectState | None:
    return ObjectStateRegistry.global_config_state(GlobalPipelineConfig)


def _edit_without_saving() -> ObjectState:
    """Change the global config's worker count and leave the change unsaved."""

    state = _global_state()
    state.update_parameter("num_workers", EDITED_WORKERS)
    return state


def _assert_edit_is_still_unsaved(state: ObjectState) -> None:
    assert _global_state() is state
    assert get_live_global_config(GlobalPipelineConfig).num_workers == EDITED_WORKERS
    assert get_saved_global_config(GlobalPipelineConfig).num_workers == SAVED_WORKERS
    assert "num_workers" in state.dirty_fields


def _write_imagexpress_plate(root: Path) -> Path:
    """The smallest plate directory the ImageXpress handler initialises."""

    plate = root / "plate"
    images = plate / "TimePoint_1"
    images.mkdir(parents=True)
    (images / "plate_A01_s1_w1.tif").write_bytes(b"")
    (plate / "plate.HTD").write_text(
        '"XSites", 1\n"YSites", 1\n"PixelSizeUM", 0.5\n"WaveName1", "DAPI"', encoding="utf-8"
    )
    return plate


class ServerStandIn:
    """Compilation and submission answered in-process; keeps what was submitted."""

    def __init__(self, session, monkeypatch) -> None:
        self.submitted_global_configs: list[GlobalPipelineConfig] = []
        monkeypatch.setattr(compile_batch_module, "submit_compile", self._submit_compile)
        monkeypatch.setattr(compile_batch_module, "wait_for_compile", self._wait_for_compile)
        monkeypatch.setattr(session, "connect_client", self._connect)
        monkeypatch.setattr(session.client, "require_client", lambda: object())
        monkeypatch.setattr(
            session.submission, "submit_execution", self._submit_execution
        )

    async def _connect(self):
        return object()

    async def _submit_compile(self, client, request) -> str:
        return f"compile-{request.name}"

    async def _wait_for_compile(self, client, *, execution_id: str, scope_id: str):
        return CompiledArtifactInspection(
            compile_artifact_id=execution_id, subject_id=scope_id, steps=()
        )

    async def _submit_execution(self, request, **_options) -> None:
        self.submitted_global_configs.append(request.global_config)


def test_headless_session_keeps_one_global_state_until_it_closes(
    tmp_path: Path
) -> None:
    with OpenHCSAgentContext(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        ),
        session_transport_config=OpenHCSZMQConfig(
            default_port=session_port(), persistent=False
        ),
    ) as context:
        assert _global_state() is None

        session = context.session
        state = _global_state()
        assert state is not None

        (scope_id,) = add_datasets(session, tmp_path, "plate")
        assert _global_state() is state
        assert ObjectStateRegistry.get_by_scope(scope_id) is not None

        session.apply_global_config(GlobalPipelineConfig(num_workers=EDITED_WORKERS))
        assert _global_state() is state

    assert _global_state() is None
    assert get_saved_global_config(GlobalPipelineConfig) is None


def test_agent_context_closes_only_the_session_it_opened() -> None:
    with caller_session() as session:
        state = _global_state()
        with OpenHCSAgentContext(session=session) as context:
            assert context.session is session
        assert _global_state() is state
        session.apply_global_config(GlobalPipelineConfig(num_workers=EDITED_WORKERS))
        assert _global_state() is state

    assert _global_state() is None


def test_closing_a_session_leaves_a_later_sessions_state_registered() -> None:
    with caller_session() as first:
        with caller_session():
            state = _global_state()
            first.close()
            assert _global_state() is state
        assert _global_state() is None


def test_gui_session_keeps_one_global_state_until_it_closes(tmp_path: Path) -> None:
    with session_gui() as gui:
        state = _global_state()
        assert state is not None

        add_datasets(gui.session, tmp_path, "plate")
        gui.settle()
        assert _global_state() is state

        gui.session.apply_global_config(GlobalPipelineConfig(num_workers=EDITED_WORKERS))
        gui.settle()
        assert _global_state() is state

    assert _global_state() is None


def test_adding_a_dataset_keeps_an_unsaved_global_edit(tmp_path: Path) -> None:
    with caller_session(global_config=GlobalPipelineConfig(num_workers=SAVED_WORKERS)) as session:
        state = _edit_without_saving()

        (scope_id,) = add_datasets(session, tmp_path, "plate")

        _assert_edit_is_still_unsaved(state)
        dataset_state = ObjectStateRegistry.get_by_scope(scope_id)
        assert dataset_state.get_resolved_value("num_workers") == EDITED_WORKERS
        assert dataset_state.get_saved_resolved_value("num_workers") == SAVED_WORKERS


def test_initialising_a_dataset_keeps_an_unsaved_global_edit(tmp_path: Path) -> None:
    with caller_session(
        global_config=GlobalPipelineConfig(num_workers=SAVED_WORKERS),
        workspace_root=tmp_path / "workspaces",
    ) as session:
        (scope_id,) = session.add_dataset_roots([_write_imagexpress_plate(tmp_path)])
        state = _edit_without_saving()

        asyncio.run(session.initialize_datasets((scope_id,)))

        assert session.orchestrator(scope_id).state is OrchestratorReady
        _assert_edit_is_still_unsaved(state)


def test_compiling_a_dataset_keeps_an_unsaved_global_edit(
    tmp_path: Path, monkeypatch
) -> None:
    with caller_session(global_config=GlobalPipelineConfig(num_workers=SAVED_WORKERS)) as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        session.set_dataset_state(scope_id, OrchestratorReady)
        ServerStandIn(session, monkeypatch)
        state = _edit_without_saving()

        asyncio.run(session.compile_datasets((scope_id,)))

        assert session.compiled_inspection(scope_id) is not None
        _assert_edit_is_still_unsaved(state)


def test_running_a_dataset_submits_the_saved_global_config_and_keeps_the_unsaved_edit(
    tmp_path: Path, monkeypatch
) -> None:
    with caller_session(global_config=GlobalPipelineConfig(num_workers=SAVED_WORKERS)) as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        session.set_dataset_state(scope_id, OrchestratorReady)
        server = ServerStandIn(session, monkeypatch)
        state = _edit_without_saving()

        asyncio.run(session.run_datasets((scope_id,)))

        assert [config.num_workers for config in server.submitted_global_configs] == [
            SAVED_WORKERS
        ]
        _assert_edit_is_still_unsaved(state)


def test_replacing_the_global_config_replaces_live_and_saved_and_datasets_follow(
    tmp_path: Path,
) -> None:
    with caller_session(global_config=GlobalPipelineConfig(num_workers=SAVED_WORKERS)) as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        dataset_state = ObjectStateRegistry.get_by_scope(scope_id)
        state = _edit_without_saving()

        session.apply_global_config(GlobalPipelineConfig(num_workers=5))

        assert get_live_global_config(GlobalPipelineConfig).num_workers == 5
        assert get_saved_global_config(GlobalPipelineConfig).num_workers == 5
        assert not state.dirty_fields
        assert dataset_state.get_resolved_value("num_workers") == 5
        assert dataset_state.get_saved_resolved_value("num_workers") == 5
        assert not dataset_state.dirty_fields


def test_another_thread_reads_the_session_global_config(tmp_path: Path) -> None:
    with caller_session(global_config=GlobalPipelineConfig(num_workers=SAVED_WORKERS)) as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        dataset_state = ObjectStateRegistry.get_by_scope(scope_id)
        _edit_without_saving()
        seen: dict[str, int] = {}

        def read() -> None:
            seen["saved global"] = get_saved_global_config(GlobalPipelineConfig).num_workers
            seen["live global"] = get_live_global_config(GlobalPipelineConfig).num_workers
            seen["dataset saved"] = dataset_state.get_saved_resolved_value("num_workers")
            seen["dataset live"] = dataset_state.get_resolved_value("num_workers")

        thread = threading.Thread(target=read)
        thread.start()
        thread.join()

        assert seen == {
            "saved global": SAVED_WORKERS,
            "live global": EDITED_WORKERS,
            "dataset saved": SAVED_WORKERS,
            "dataset live": EDITED_WORKERS,
        }
