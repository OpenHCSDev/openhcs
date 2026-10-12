"""What editing, cancelling and saving in a config window does to the configs it shows.

The first group drives the application's global config window: the registered
global state holds the global config, a dataset inherits from it, and a save
writes the config file. The second group covers what a save of any config window
keeps when part of it fails.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace

import pytest
from formbridge.services.service_registry import ServiceRegistry
from objectstate import (
    ObjectState,
    ObjectStateRegistry,
    get_live_global_config,
    get_saved_global_config,
)
from PyQt6.QtWidgets import QDialog, QMessageBox
from pyqt_reactive.services.scope_window_factory import ScopeWindowCreationRequest
from pyqt_reactive.windows.config_window import (
    ConfigSaveParticipant,
    ConfigWindowTabSpec,
)

from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.config_cache import (
    ConfigCacheSpec,
    global_pipeline_config_cache_spec,
    load_config_sync,
    save_global_config_sync,
)
from openhcs.pyqt_gui.config import UIConfig, get_default_ui_config
from openhcs.pyqt_gui.services.ui_window_ids import OpenHCSUiWindowId
from openhcs.pyqt_gui.services.window_handlers import OpenHCSWindowCreationAuthority
from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget
from openhcs.pyqt_gui.windows.config_window import OpenHCSConfigDocument, OpenHCSConfigWindow
from tests.unit.pyqt_gui.session_harness import add_datasets, caller_session


@dataclass(frozen=True)
class _FirstConfig:
    value: int = 1


@dataclass(frozen=True)
class _SecondConfig:
    value: int = 1


@pytest.fixture(autouse=True)
def _clear_object_state_registry():
    yield


@pytest.fixture
def error_dialogs(monkeypatch) -> list[str]:
    """The messages of the error dialogs a window showed."""

    messages: list[str] = []
    monkeypatch.setattr(
        QMessageBox,
        "critical",
        lambda _parent, _title, message: messages.append(message),
    )
    return messages


def _dispose_window(window: OpenHCSConfigWindow, qapp) -> None:
    """Close the window, which also stops a form that is still being built."""

    window.close()
    window.deleteLater()
    qapp.processEvents()


# -- the application's global config window ----------------------------------


@dataclass
class GlobalConfigEditing:
    """The global config window open over a session with one dataset."""

    window: OpenHCSConfigWindow
    dataset: ObjectState
    config_file: Path
    main_window_configs: list[int] = field(default_factory=list)
    refuse_ui_config: bool = False

    def workers(self) -> tuple[int, int, int, int]:
        """``num_workers``: live and saved global config, then what the dataset inherits."""

        return (
            get_live_global_config(GlobalPipelineConfig).num_workers,
            get_saved_global_config(GlobalPipelineConfig).num_workers,
            self.dataset.get_resolved_value("num_workers"),
            self.dataset.get_saved_resolved_value("num_workers"),
        )

    def workers_on_disk(self) -> int:
        on_disk = load_config_sync(ConfigCacheSpec(GlobalPipelineConfig, self.config_file))
        return on_disk.num_workers

    def set_workers_in_form(self, count: int) -> None:
        self.window.form_manager.update_parameter("num_workers", count)

    def set_workers_in_code_editor(self, count: int) -> None:
        """Apply an edited config document, as the window's code editor does on save."""

        source = OpenHCSConfigDocument().render(
            GlobalPipelineConfig(num_workers=count),
            expected_config_type=GlobalPipelineConfig,
            clean_mode=True,
        )
        self.window.window_code_document_driver().apply_source(source)

    def take_ui_config(self, _config: UIConfig) -> None:
        if self.refuse_ui_config:
            raise RuntimeError("the main window refused the UI config")


@pytest.fixture
def editing(qapp, tmp_path, monkeypatch) -> Iterator[GlobalConfigEditing]:
    """Open the global config window the way the application does.

    The session registers the global state, the config file holds the saved
    config (one worker), and a dataset inherits ``num_workers`` from it.
    """

    monkeypatch.setenv("XDG_DATA_HOME", str(tmp_path / "data"))
    initial = GlobalPipelineConfig(num_workers=1)
    assert save_global_config_sync(initial)
    with caller_session(global_config=initial) as session:
        (dataset_scope,) = add_datasets(session, tmp_path, "plate")
        ObjectStateRegistry.register(
            ObjectState(get_default_ui_config(), scope_id=UIConfig.object_state_scope_id())
        )
        opened = GlobalConfigEditing(
            window=None,
            dataset=ObjectStateRegistry.get_by_scope(dataset_scope),
            config_file=global_pipeline_config_cache_spec().cache_file,
        )
        main_window = SimpleNamespace(
            config_changed=SimpleNamespace(
                emit=lambda config: opened.main_window_configs.append(config.num_workers)
            ),
            set_ui_config=opened.take_ui_config,
        )
        ServiceRegistry.register(
            PlateManagerWidget,
            SimpleNamespace(
                session=session,
                service_adapter=SimpleNamespace(main_window=main_window),
            ),
        )
        opened.window = OpenHCSWindowCreationAuthority().create_global_config_window(
            ScopeWindowCreationRequest(scope_id=OpenHCSUiWindowId.global_config)
        )
        qapp.processEvents()
        try:
            yield opened
        finally:
            ServiceRegistry.unregister(PlateManagerWidget)
            _dispose_window(opened.window, qapp)


def test_a_form_edit_changes_the_live_global_config_and_leaves_the_saved_one(
    editing: GlobalConfigEditing,
) -> None:
    assert editing.workers() == (1, 1, 1, 1)

    editing.set_workers_in_form(3)

    assert editing.workers() == (3, 1, 3, 1)
    assert editing.workers_on_disk() == 1
    assert editing.main_window_configs == []


def test_a_code_edit_changes_the_live_global_config_and_only_a_save_saves_it(
    editing: GlobalConfigEditing,
) -> None:
    editing.set_workers_in_code_editor(5)

    assert editing.workers() == (5, 1, 5, 1)
    assert editing.workers_on_disk() == 1

    editing.window.save_config(close_window=False)

    assert editing.workers() == (5, 5, 5, 5)
    assert editing.workers_on_disk() == 5


def test_cancel_puts_the_live_global_config_back_to_the_saved_one(
    editing: GlobalConfigEditing,
) -> None:
    editing.set_workers_in_form(3)

    editing.window.reject()

    assert editing.workers() == (1, 1, 1, 1)
    assert editing.workers_on_disk() == 1
    assert editing.main_window_configs == []


def test_save_makes_the_edit_the_saved_global_config_and_writes_the_config_file(
    editing: GlobalConfigEditing,
    error_dialogs: list[str],
) -> None:
    editing.set_workers_in_form(3)

    editing.window.save_config(close_window=False)

    assert editing.workers() == (3, 3, 3, 3)
    assert editing.workers_on_disk() == 3
    assert editing.main_window_configs == [3]
    assert error_dialogs == []


def test_a_save_that_cannot_write_the_config_file_keeps_the_edit_unsaved(
    editing: GlobalConfigEditing,
    error_dialogs: list[str],
) -> None:
    """The edit stays in the window; nothing else learns of it; cancel still works."""

    editing.set_workers_in_form(3)
    config_directory = editing.config_file.parent
    config_directory.chmod(0o500)
    try:
        editing.window.save_config(close_window=False)
    finally:
        config_directory.chmod(0o700)

    assert editing.workers() == (3, 1, 3, 1)
    assert editing.workers_on_disk() == 1
    assert editing.main_window_configs == []
    assert len(error_dialogs) == 1
    assert "Failed to persist GlobalPipelineConfig." in error_dialogs[0]

    editing.window.reject()

    assert editing.workers() == (1, 1, 1, 1)


def test_a_save_refused_after_the_config_file_was_written_writes_the_previous_config_back(
    editing: GlobalConfigEditing,
    error_dialogs: list[str],
) -> None:
    """The UI config tab refuses its part after the global config reached disk."""

    editing.set_workers_in_form(3)
    editing.refuse_ui_config = True

    editing.window.save_config(close_window=False)

    assert editing.workers() == (3, 1, 3, 1)
    assert editing.workers_on_disk() == 1
    assert editing.main_window_configs == [3, 1]
    assert error_dialogs == [
        "Failed to save configuration:\nthe main window refused the UI config"
    ]


# -- any config window --------------------------------------------------------


def test_a_save_refused_before_it_starts_changes_nothing(
    qapp,
    error_dialogs: list[str],
) -> None:
    state = ObjectState(_FirstConfig(), scope_id="guard")
    ObjectStateRegistry.register(state, _skip_snapshot=True)
    effects: list[tuple[str, object]] = []

    refusing = [True]

    def reject_mutation() -> None:
        if refusing:
            raise RuntimeError("mutation rejected")

    window = OpenHCSConfigWindow(
        tabs=(
            ConfigWindowTabSpec(
                state=state,
                save_participant=ConfigSaveParticipant(
                    apply=lambda value: effects.append(("apply", value)),
                    rollback=lambda value: effects.append(("rollback", value)),
                ),
                before_mutation=reject_mutation,
            ),
        ),
        scope_id="guard",
    )

    try:
        state.update_parameter("value", 2)
        qapp.processEvents()
        token_before = ObjectStateRegistry.get_token()
        saved_before = state.saved_object

        window.save_config(close_window=False)

        assert ObjectStateRegistry.get_token() == token_before
        assert state.saved_object is saved_before
        assert state.parameters["value"] == 2
        assert state.is_raw_dirty is True
        assert effects == []
        assert error_dialogs == ["Failed to save configuration:\nmutation rejected"]
    finally:
        refusing.clear()  # closing is a mutation too; a refused close asks the user
        _dispose_window(window, qapp)


def test_a_save_failing_at_the_second_tab_leaves_both_tabs_unsaved(
    qapp,
    monkeypatch,
    error_dialogs: list[str],
) -> None:
    first_saved = _FirstConfig()
    second_saved = _SecondConfig()
    first_state = ObjectState(first_saved, scope_id="first")
    second_state = ObjectState(second_saved, scope_id="second")
    ObjectStateRegistry.register(first_state, _skip_snapshot=True)
    ObjectStateRegistry.register(second_state, _skip_snapshot=True)
    window = OpenHCSConfigWindow(
        tabs=(
            ConfigWindowTabSpec(state=first_state),
            ConfigWindowTabSpec(state=second_state),
        ),
        scope_id="",
    )

    try:
        first_state.update_parameter("value", 2)
        second_state.update_parameter("value", 3)
        monkeypatch.setattr(
            second_state,
            "mark_saved",
            lambda: (_ for _ in ()).throw(RuntimeError("second mark_saved failed")),
        )

        window.save_config(close_window=False)

        assert first_state.saved_object is first_saved
        assert second_state.saved_object is second_saved
        assert first_state.parameters["value"] == 2
        assert second_state.parameters["value"] == 3
        assert first_state.is_raw_dirty is True
        assert second_state.is_raw_dirty is True
        assert error_dialogs == ["Failed to save configuration:\nsecond mark_saved failed"]
    finally:
        _dispose_window(window, qapp)


def test_a_failing_save_participant_undoes_the_attempted_ones_newest_first(
    qapp,
    error_dialogs: list[str],
) -> None:
    first_saved = _FirstConfig()
    second_saved = _SecondConfig()
    first_state = ObjectState(first_saved, scope_id="first")
    second_state = ObjectState(second_saved, scope_id="second")
    ObjectStateRegistry.register(first_state, _skip_snapshot=True)
    ObjectStateRegistry.register(second_state, _skip_snapshot=True)
    effects: list[tuple[str, object]] = []

    def fail_second(value: object) -> None:
        effects.append(("apply_second", value))
        raise RuntimeError("second participant failed")

    window = OpenHCSConfigWindow(
        tabs=(
            ConfigWindowTabSpec(
                state=first_state,
                save_participant=ConfigSaveParticipant(
                    apply=lambda value: effects.append(("apply_first", value)),
                    rollback=lambda value: effects.append(("rollback_first", value)),
                ),
            ),
            ConfigWindowTabSpec(
                state=second_state,
                save_participant=ConfigSaveParticipant(
                    apply=fail_second,
                    rollback=lambda value: effects.append(("rollback_second", value)),
                ),
            ),
        ),
        scope_id="",
    )

    try:
        first_state.update_parameter("value", 2)
        second_state.update_parameter("value", 3)

        window.save_config(close_window=False)

        assert effects == [
            ("apply_first", _FirstConfig(value=2)),
            ("apply_second", _SecondConfig(value=3)),
            ("rollback_second", second_saved),
            ("rollback_first", first_saved),
        ]
        assert first_state.saved_object is first_saved
        assert second_state.saved_object is second_saved
        assert first_state.is_raw_dirty is True
        assert second_state.is_raw_dirty is True
        assert error_dialogs == ["Failed to save configuration:\nsecond participant failed"]
    finally:
        _dispose_window(window, qapp)


def test_a_failure_while_closing_after_a_save_keeps_the_save(
    qapp,
    monkeypatch,
    error_dialogs: list[str],
) -> None:
    state = ObjectState(_FirstConfig(), scope_id="postcommit")
    ObjectStateRegistry.register(state, _skip_snapshot=True)
    applied: list[object] = []
    rolled_back: list[object] = []
    window = OpenHCSConfigWindow(
        tabs=(
            ConfigWindowTabSpec(
                state=state,
                save_participant=ConfigSaveParticipant(
                    apply=applied.append,
                    rollback=rolled_back.append,
                ),
            ),
        ),
        scope_id="postcommit",
    )

    try:
        state.update_parameter("value", 2)
        monkeypatch.setattr(
            window,
            "accept_committed_state",
            lambda: (_ for _ in ()).throw(RuntimeError("postcommit close failed")),
        )

        window.save_config()

        assert state.saved_object == _FirstConfig(value=2)
        assert state.is_raw_dirty is False
        assert applied == [_FirstConfig(value=2)]
        assert rolled_back == []
        assert error_dialogs == []
    finally:
        _dispose_window(window, qapp)


def test_a_tab_that_cannot_be_built_is_reported_and_closes_the_window(
    qapp,
    monkeypatch,
    error_dialogs: list[str],
) -> None:
    first_state = ObjectState(_FirstConfig(), scope_id="first")
    second_state = ObjectState(_SecondConfig(), scope_id="second")
    build_tab = OpenHCSConfigWindow._materialize_tab

    def build_or_fail(self, tab):
        if tab.spec.label == "_SecondConfig":
            raise RuntimeError("inactive tab build failed")
        return build_tab(self, tab)

    monkeypatch.setattr(OpenHCSConfigWindow, "_materialize_tab", build_or_fail)
    window = OpenHCSConfigWindow(
        tabs=(
            ConfigWindowTabSpec(state=first_state),
            ConfigWindowTabSpec(state=second_state),
        ),
        scope_id="",
    )

    window.show()
    qapp.processEvents()
    window._tab_body.set_current_index(1)
    qapp.processEvents()

    assert window.active_tab.spec.label == "_FirstConfig"
    assert window.result() == QDialog.DialogCode.Rejected
    assert error_dialogs == ["Failed to construct _SecondConfig:\ninactive tab build failed"]


def test_a_form_row_that_fails_to_build_later_is_reported_and_closes_the_window(
    qapp,
    error_dialogs: list[str],
) -> None:
    state = ObjectState(_FirstConfig(), scope_id="progressive")
    window = OpenHCSConfigWindow(
        tabs=(ConfigWindowTabSpec(state=state),),
        scope_id="progressive",
    )
    window.show()
    qapp.processEvents()

    window.form_manager.form_build_failed.emit(RuntimeError("later row failed"))
    qapp.processEvents()

    assert window.result() == QDialog.DialogCode.Rejected
    assert error_dialogs == ["Failed to construct _FirstConfig:\nlater row failed"]


def test_closing_a_window_whose_form_is_still_building_stops_the_build_quietly(
    qapp,
    error_dialogs: list[str],
) -> None:
    state = ObjectState(GlobalPipelineConfig(), scope_id="progressive-close")
    window = OpenHCSConfigWindow(
        tabs=(ConfigWindowTabSpec(state=state),),
        scope_id="progressive-close",
    )
    manager = window.form_manager

    assert manager.form_build_complete is False

    window.close()
    for _ in range(10):
        qapp.processEvents()

    assert manager.form_build_cancelled is True
    assert manager.form_build_failure is None
    assert error_dialogs == []
