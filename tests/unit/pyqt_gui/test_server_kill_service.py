from openhcs.pyqt_gui.widgets.shared.server_browser import (
    ServerKillPlan,
    ServerKillService,
)


class _FakeRegistry:
    def __init__(self):
        self.removed: list[int] = []

    def remove_tracker(self, port: int) -> None:
        self.removed.append(port)


def test_server_kill_service_strict_failures_returns_error():
    registry = _FakeRegistry()
    killed_ports: list[int] = []

    def kill_server_fn(port: int, graceful: bool, config) -> bool:
        if port == 7778:
            return False
        return True

    service = ServerKillService(
        kill_server_fn=kill_server_fn,
        queue_tracker_registry_factory=lambda: registry,
        config=object(),
    )
    plan = ServerKillPlan(
        graceful=True,
        strict_failures=True,
        emit_signal_on_failure=False,
        success_message="ok",
    )

    success, message = service.kill_ports(
        ports=[7777, 7778],
        plan=plan,
        on_server_killed=lambda port: killed_ports.append(port),
        log_info=lambda *_args, **_kwargs: None,
        log_warning=lambda *_args, **_kwargs: None,
        log_error=lambda *_args, **_kwargs: None,
    )

    assert not success
    assert "7778" in message
    assert killed_ports == [7777]
    assert registry.removed == [7777]


def test_server_kill_service_emit_on_failure_marks_killed_for_refresh():
    registry = _FakeRegistry()
    killed_ports: list[int] = []

    def kill_server_fn(port: int, graceful: bool, config) -> bool:
        return False

    service = ServerKillService(
        kill_server_fn=kill_server_fn,
        queue_tracker_registry_factory=lambda: registry,
        config=object(),
    )
    plan = ServerKillPlan(
        graceful=False,
        strict_failures=False,
        emit_signal_on_failure=True,
        success_message="done",
    )

    success, message = service.kill_ports(
        ports=[8888, 9999],
        plan=plan,
        on_server_killed=lambda port: killed_ports.append(port),
        log_info=lambda *_args, **_kwargs: None,
        log_warning=lambda *_args, **_kwargs: None,
        log_error=lambda *_args, **_kwargs: None,
    )

    assert success
    assert message == "done"
    assert killed_ports == [8888, 9999]
    assert registry.removed == [8888, 9999]
