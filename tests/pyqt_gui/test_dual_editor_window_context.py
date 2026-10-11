from openhcs.authoring.session.events import (
    GlobalConfigChanged,
    PipelineChanged,
    PipelineImported,
)
from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow


class DummyServiceAdapter:
    def __init__(self) -> None:
        self.main_window = object()


def test_dual_editor_window_uses_explicit_service_adapter_context() -> None:
    window = DualEditorWindow.__new__(DualEditorWindow)
    window.service_adapter = DummyServiceAdapter()

    assert window._find_main_window() is window.service_adapter.main_window


class RecordingSignal:
    def __init__(self) -> None:
        self.connected = []
        self.disconnected = []

    def connect(self, callback) -> None:
        self.connected.append(callback)

    def disconnect(self, callback) -> None:
        self.disconnected.append(callback)


class RecordingRelay:
    def __init__(self) -> None:
        self.closed = False

    def close(self) -> None:
        self.closed = True


def test_dual_editor_window_cleans_cross_window_subscriptions() -> None:
    window = DualEditorWindow.__new__(DualEditorWindow)
    relay = RecordingRelay()
    orchestrator_signal = RecordingSignal()
    window._session_events = relay
    window._orchestrator_config_signal = orchestrator_signal
    window._compiled_artifact_signal = None
    window._runtime_artifact_signal = None
    window._debug_snapshot_signal = None
    window._managed_resource_cleanup_done = False
    window.step_editor = None

    window._cleanup_managed_resources()

    assert relay.closed
    assert orchestrator_signal.disconnected == [window.on_orchestrator_config_changed]
    assert window._session_events is None
    assert window._orchestrator_config_signal is None


def test_dual_editor_window_orchestrator_signal_connection_is_owned() -> None:
    window = DualEditorWindow.__new__(DualEditorWindow)
    signal = RecordingSignal()

    window.connect_orchestrator_config_signal(signal)

    assert signal.connected == [window.on_orchestrator_config_changed]
    assert window._orchestrator_config_signal is signal


class PipelineSession:
    def __init__(self) -> None:
        self.steps = {"/plate1": ["a", "b"], "/plate2": ["c"]}

    def pipeline_steps(self, scope_id: str) -> list:
        return self.steps[scope_id]


def test_dual_editor_follows_its_own_plates_pipeline_changes(monkeypatch) -> None:
    window = DualEditorWindow.__new__(DualEditorWindow)
    window._session = PipelineSession()
    window.plate_scope = "/plate1"
    followed = []
    monkeypatch.setattr(window, "_on_pipeline_changed", followed.append)

    window.on_session_event(PipelineChanged(dataset_scope_id="/plate2"))
    window.on_session_event(PipelineChanged(dataset_scope_id="/plate1"))
    window.on_session_event(PipelineImported(dataset_scope_id="/plate1"))

    assert followed == [["a", "b"], ["a", "b"]]


def test_dual_editor_reresolves_placeholders_on_global_config_change(monkeypatch) -> None:
    from objectstate.object_state import ObjectStateRegistry

    window = DualEditorWindow.__new__(DualEditorWindow)
    tokens = []
    monkeypatch.setattr(ObjectStateRegistry, "increment_token", lambda: tokens.append(1))

    window.on_session_event(GlobalConfigChanged(config=object()))

    assert tokens == [1]
