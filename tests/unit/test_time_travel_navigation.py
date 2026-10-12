from pyqt_reactive.services.time_travel_navigation import TimeTravelNavigator
from objectstate.object_state import ObjectState, ObjectStateRegistry
from openhcs.core.steps.function_step import FunctionStep
from formbridge.services.function_navigation import build_function_token_field_path
from pyqt_reactive.services.window_navigation import (
    WindowNavigationResult,
)
from openhcs.pyqt_gui.windows.dual_editor_window import (
    step_function_scope,
)

NAVIGATOR = TimeTravelNavigator(function_scope=step_function_scope)


class RuntimeCallable:
    def __call__(self, image, threshold: int = 1):
        return image


def _reset_registry() -> None:
    ObjectStateRegistry._states.clear()
    ObjectStateRegistry._time_travel_limbo.clear()
    ObjectStateRegistry._graveyard.clear()
    ObjectStateRegistry._snapshots.clear()
    ObjectStateRegistry._timelines.clear()
    ObjectStateRegistry._current_timeline = "main"
    ObjectStateRegistry._current_head = None
    ObjectStateRegistry._in_time_travel = False


def test_time_travel_navigation_filters_unrelated_dirty_scopes() -> None:
    triggering_scope = "/tmp/plate::functionstep_5"

    assert NAVIGATOR.includes(triggering_scope, triggering_scope)
    assert not NAVIGATOR.includes(f"{triggering_scope}::cellprofilerruntimecallable_0", triggering_scope)
    assert not NAVIGATOR.includes("/tmp/plate::functionstep_9", triggering_scope)


def test_time_travel_navigation_keeps_legacy_global_refresh_when_scope_unknown() -> (
    None
):
    assert NAVIGATOR.includes("/tmp/plate::functionstep_9", None)


def test_time_travel_navigation_includes_parent_step_for_function_trigger() -> None:
    step_scope = "/tmp/plate::functionstep_5"
    function_scope = f"{step_scope}::cellprofilerruntimecallable_0"

    assert NAVIGATOR.includes(function_scope, function_scope)
    assert NAVIGATOR.includes(step_scope, function_scope)


def test_time_travel_plate_scope_does_not_open_step_descendants() -> None:
    plate_scope = "/tmp/plate"

    assert not NAVIGATOR.includes(f"{plate_scope}::functionstep_5", plate_scope)


def test_time_travel_unknown_trigger_does_not_create_missing_windows(
    monkeypatch,
) -> None:
    _reset_registry()
    step_scope = "/tmp/plate::functionstep_5"
    step_state = ObjectState(
        FunctionStep(func=RuntimeCallable(), name="Crop"),
        scope_id=step_scope,
    )
    ObjectStateRegistry.register(step_state, _skip_snapshot=True)

    requests = []

    def fake_navigate(request):
        requests.append(request)
        return WindowNavigationResult(
            request=request,
            window=None,
            focused=False,
            created=False,
            window_scope_id=request.scope_id,
        )

    from pyqt_reactive.services.scope_window_navigation import (
        ScopeWindowNavigationService,
    )

    monkeypatch.setattr(
        ScopeWindowNavigationService,
        "navigate",
        staticmethod(fake_navigate),
    )
    scheduled: list[object] = []
    monkeypatch.setattr(
        TimeTravelNavigator,
        "defer",
        staticmethod(lambda callback: scheduled.append(callback)),
    )

    NAVIGATOR.on_time_travel_complete([(step_scope, step_state)], None)

    assert requests == []
    assert len(scheduled) == 1
    scheduled[0]()

    assert len(requests) == 1
    assert requests[0].create_if_missing is False


def test_time_travel_navigation_runs_after_later_refresh_callbacks(monkeypatch) -> None:
    _reset_registry()
    step_scope = "/tmp/plate::functionstep_5"
    field_path = "source_bindings.source_filters"
    step_state = ObjectState(
        FunctionStep(func=RuntimeCallable(), name="Crop"),
        scope_id=step_scope,
    )
    ObjectStateRegistry.register(step_state, _skip_snapshot=True)
    step_state._last_changed_field = field_path

    scheduled: list[object] = []
    monkeypatch.setattr(
        TimeTravelNavigator,
        "defer",
        staticmethod(lambda callback: scheduled.append(callback)),
    )

    class TabWidget:
        def __init__(self) -> None:
            self.indices: list[int] = []

        def setCurrentIndex(self, index: int) -> None:
            self.indices.append(index)

    class StepWindow:
        def __init__(self) -> None:
            self.tab_widget = TabWidget()

    window = StepWindow()
    navigate_requests = []

    def fake_navigate(request):
        navigate_requests.append(request)
        return WindowNavigationResult(
            request=request,
            window=window,
            focused=True,
            created=False,
            window_scope_id=request.scope_id,
        )

    from pyqt_reactive.services.scope_window_navigation import (
        ScopeWindowNavigationService,
    )

    monkeypatch.setattr(
        ScopeWindowNavigationService,
        "navigate",
        staticmethod(fake_navigate),
    )

    navigator = TimeTravelNavigator(
        function_scope=step_function_scope,
        target_shown=lambda scope_id, target: window.tab_widget.setCurrentIndex(0),
    )
    navigator.on_time_travel_complete([(step_scope, step_state)], step_scope)

    assert navigate_requests == []
    window.tab_widget.setCurrentIndex(1)

    scheduled[0]()

    assert len(navigate_requests) == 1
    assert navigate_requests[0].field_path == field_path
    assert window.tab_widget.indices == [1, 0]


def test_time_travel_function_scope_reopens_parent_step_with_parent_state() -> None:
    _reset_registry()
    step_scope = "/tmp/plate::functionstep_5"
    function_scope = f"{step_scope}::cellprofilerruntimecallable_0"
    step_state = ObjectState(
        FunctionStep(func=RuntimeCallable(), name="Crop"),
        scope_id=step_scope,
    )
    function_state = ObjectState(
        RuntimeCallable(),
        scope_id=function_scope,
        parent_state=step_state,
        initial_values={"threshold": 3},
    )
    ObjectStateRegistry.register(step_state, _skip_snapshot=True)
    ObjectStateRegistry.register(function_state, _skip_snapshot=True)

    requests = NAVIGATOR.window_requests(
        [(function_scope, function_state)],
        function_scope,
    )

    request = requests[step_scope]
    assert request.scope_id == step_scope
    assert request.object_state is step_state
    assert request.target is not None
    assert request.target.to_field_path() == build_function_token_field_path(
        "cellprofilerruntimecallable_0"
    )


def test_time_travel_step_source_bindings_child_targets_step_settings() -> None:
    _reset_registry()
    step_scope = "/tmp/plate::functionstep_5"
    field_path = "source_bindings.source_filters"
    step_state = ObjectState(
        FunctionStep(func=RuntimeCallable(), name="Crop"),
        scope_id=step_scope,
    )
    ObjectStateRegistry.register(step_state, _skip_snapshot=True)
    step_state._last_changed_field = field_path

    requests = NAVIGATOR.window_requests(
        [(step_scope, step_state)],
        step_scope,
    )

    request = requests[step_scope]
    assert request.target is not None
    assert not request.target.is_function_target
    assert request.target.to_field_path() == field_path


def test_time_travel_unknown_trigger_prefers_source_bindings_field_over_function_scope() -> (
    None
):
    _reset_registry()
    step_scope = "/tmp/plate::functionstep_5"
    function_scope = f"{step_scope}::function_0"
    field_path = "source_bindings.source_filters"
    step_state = ObjectState(
        FunctionStep(func=RuntimeCallable(), name="Crop"),
        scope_id=step_scope,
    )
    function_state = ObjectState(
        RuntimeCallable(),
        scope_id=function_scope,
        parent_state=step_state,
        initial_values={"threshold": 3},
    )
    ObjectStateRegistry.register(step_state, _skip_snapshot=True)
    ObjectStateRegistry.register(function_state, _skip_snapshot=True)
    step_state._last_changed_field = field_path

    function_first = NAVIGATOR.window_requests(
        [(function_scope, function_state), (step_scope, step_state)],
        None,
    )
    step_first = NAVIGATOR.window_requests(
        [(step_scope, step_state), (function_scope, function_state)],
        None,
    )

    assert function_first[step_scope].target is not None
    assert function_first[step_scope].target.to_field_path() == field_path
    assert not function_first[step_scope].target.is_function_target
    assert step_first[step_scope].target is not None
    assert step_first[step_scope].target.to_field_path() == field_path
    assert not step_first[step_scope].target.is_function_target
