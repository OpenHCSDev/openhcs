"""Native painter-to-bridge async capture and declared wire-result decoding."""

from dataclasses import dataclass

import pytest
from PyQt6.QtCore import QEvent
from PyQt6.QtWidgets import QDialog, QVBoxLayout

from openhcs.agent.dto.ui_bridge import UiWindowSnapshotRequest, UiWindowSnapshotResult
from openhcs.agent.services.ui_bridge_service import UiBridgeOperationContractABC
from openhcs.agent.services.ui_bridge_transport import AgentDtoJsonCodec
from openhcs.pyqt_gui.services.ui_agent_bridge import UiAgentBridgeService
from openhcs.pyqt_gui.services.ui_bridge_windows import QtTopLevelWindowProjection
from openhcs.serialization.json import to_jsonable
from pyqt_reactive.services.window_snapshot import WindowSnapshotFrameCondition


@pytest.fixture
def native_snapshot_bridge(qapp):
    import objectstate.config as config_module
    from objectstate import ObjectState, ObjectStateRegistry, set_base_config_type
    from pyqt_reactive.animation.flash_mixin import (
        WindowFlashOverlay,
        _GlobalFlashCoordinator,
    )
    from pyqt_reactive.forms.parameter_form_manager import (
        FormManagerConfig,
        ParameterFormManager,
    )
    from pyqt_reactive.theming import ColorScheme

    @dataclass
    class Fields:
        number: int = 3

    previous_base = config_module._base_config_type
    ObjectStateRegistry.clear()
    set_base_config_type(Fields)
    window = QDialog()
    window.setWindowTitle("Snapshot engineering fixture")
    window.resize(420, 180)
    form = ParameterFormManager(
        ObjectState(Fields()),
        FormManagerConfig(
            color_scheme=ColorScheme(),
            use_scroll_area=False,
        ),
    )
    QVBoxLayout(window).addWidget(form)
    window.show()
    qapp.processEvents()
    projection = QtTopLevelWindowProjection(None)
    bridge = UiAgentBridgeService()
    bridge.register_window_provider(projection)
    window_id = projection.summary(window).window_id
    yield bridge, form, window_id
    bridge.close()
    coordinator = _GlobalFlashCoordinator.get()
    if coordinator._timer is not None:
        coordinator._timer.stop()
    coordinator._computed_colors.clear()
    coordinator._playbacks.clear()
    coordinator._pending_flash_keys.clear()
    coordinator._active_windows.clear()
    WindowFlashOverlay.cleanup_window(window)
    window.close()
    window.deleteLater()
    qapp.sendPostedEvents(None, QEvent.Type.DeferredDelete)
    qapp.processEvents()
    ObjectStateRegistry.clear()
    config_module._base_config_type = previous_base


def test_async_snapshot_uses_existing_operation_and_registered_response_contract(
    qtbot,
    native_snapshot_bridge,
    tmp_path,
):
    bridge, form, window_id = native_snapshot_bridge
    request = UiWindowSnapshotRequest.from_fields(
        window_id=window_id,
        output_dir_path=str(tmp_path),
        frame_condition=WindowSnapshotFrameCondition.FLASH_MAXIMUM_ALPHA.value,
        observation_timeout_s=1.0,
    )
    accepted = bridge.snapshot_window(request)
    assert accepted.operation_id
    assert not accepted.captured
    # A capture observation must not occupy the ordinary mutation gate.
    assert bridge._mutation_gate._lock.acquire(blocking=False)
    bridge._mutation_gate._lock.release()
    form.update_parameter("number", 8)
    qtbot.waitUntil(
        lambda: bridge.get_operation_status(accepted.operation_id).completed_at_unix
        is not None,
        timeout=2000,
    )
    operation = bridge.get_operation_status(accepted.operation_id)
    assert operation.status == "completed"
    contract = UiBridgeOperationContractABC.for_name(operation.identity.operation_name)
    result = AgentDtoJsonCodec.dataclass_from_json(
        contract.response_type, operation.result_payload
    )
    assert isinstance(result, UiWindowSnapshotResult)
    assert result.captured
    assert result.frame_condition is request.frame_condition
    assert result.observation.frame.has_maximum_alpha
    assert result.resource.path.endswith(".png")
    wire_operation = AgentDtoJsonCodec.dataclass_from_json(
        type(operation), to_jsonable(operation)
    )
    assert wire_operation == operation
    wire_result = AgentDtoJsonCodec.dataclass_from_json(
        contract.response_type,
        wire_operation.result_payload,
    )
    assert wire_result == result


def test_immediate_snapshot_preserves_synchronous_result(
    native_snapshot_bridge, tmp_path
):
    bridge, form, window_id = native_snapshot_bridge
    result = bridge.snapshot_window(
        UiWindowSnapshotRequest.from_fields(
            window_id=window_id,
            output_dir_path=str(tmp_path),
        )
    )
    assert result.captured
    assert result.operation_id is result.observation is None


def test_async_snapshot_invalid_baseline_is_terminal_failed(
    qapp,
    native_snapshot_bridge,
    tmp_path,
):
    bridge, form, window_id = native_snapshot_bridge
    form.update_parameter("number", 8)
    qapp.processEvents()
    result = bridge.snapshot_window(
        UiWindowSnapshotRequest.from_fields(
            window_id=window_id,
            output_dir_path=str(tmp_path),
            frame_condition=WindowSnapshotFrameCondition.NO_FLASH.value,
            observation_timeout_s=1.0,
        )
    )
    assert not result.captured
    assert result.errors
    assert bridge.get_operation_status(result.operation_id).status == "failed"


def test_noop_reset_quiet_operation_preserves_actual_interval_receipt(
    qtbot,
    native_snapshot_bridge,
    tmp_path,
):
    bridge, form, window_id = native_snapshot_bridge
    accepted = bridge.snapshot_window(
        UiWindowSnapshotRequest.from_fields(
            window_id=window_id,
            output_dir_path=str(tmp_path),
            frame_condition=WindowSnapshotFrameCondition.NO_FLASH.value,
            observation_timeout_s=1.0,
        )
    )
    form.reset_buttons["number"].click()
    qtbot.waitUntil(
        lambda: bridge.get_operation_status(accepted.operation_id).completed_at_unix
        is not None,
        timeout=2000,
    )
    operation = bridge.get_operation_status(accepted.operation_id)
    contract = UiBridgeOperationContractABC.for_name(operation.identity.operation_name)
    result = AgentDtoJsonCodec.dataclass_from_json(
        contract.response_type, operation.result_payload
    )
    assert result.captured
    assert (
        result.observation.flash_start_count
        == result.observation.painted_frame_count
        == 0
    )
    assert (
        result.observation.completed_at_monotonic
        - result.observation.started_at_monotonic
        >= result.observation.configured_flash_duration_s
    )


def test_failed_observation_frame_and_existing_trace_decode_through_registered_owner(
    qtbot,
    native_snapshot_bridge,
    tmp_path,
):
    from pyqt_reactive.flash_trace import FlashTraceRecord
    from pyqt_reactive.services.window_snapshot import FlashPaintFrame

    bridge, form, window_id = native_snapshot_bridge
    accepted = bridge.snapshot_window(
        UiWindowSnapshotRequest.from_fields(
            window_id=window_id,
            output_dir_path=str(tmp_path),
            frame_condition=WindowSnapshotFrameCondition.NO_FLASH.value,
            observation_timeout_s=1.0,
        )
    )
    form.update_parameter("number", 8)
    qtbot.waitUntil(
        lambda: bridge.get_operation_status(accepted.operation_id).completed_at_unix
        is not None,
        timeout=2000,
    )
    operation = bridge.get_operation_status(accepted.operation_id)
    assert operation.status == "failed"
    contract = UiBridgeOperationContractABC.for_name(operation.identity.operation_name)
    result = AgentDtoJsonCodec.dataclass_from_json(
        contract.response_type, operation.result_payload
    )
    assert not result.captured and result.resource is None
    assert isinstance(result.observation.frame, FlashPaintFrame)
    assert result.observation.trace and len(result.observation.trace) <= 300
    assert all(
        isinstance(record, FlashTraceRecord) for record in result.observation.trace
    )
    assert (
        AgentDtoJsonCodec.dataclass_from_json(type(result), to_jsonable(result))
        == result
    )


def test_snapshot_cli_derives_typed_observation_arguments(tmp_path):
    from openhcs.mcp import dev_client

    parser = dev_client._build_parser()
    args = parser.parse_args(
        (
            "window-snapshot",
            "main_window",
            "--output-dir-path",
            str(tmp_path),
            "--frame-condition",
            "no_flash",
            "--observation-timeout-s",
            "2.5",
        )
    )
    call = dev_client._calls_from_args(args)[0]
    assert call.arguments["frame_condition"] == "no_flash"
    assert call.arguments["observation_timeout_s"] == 2.5


@pytest.mark.parametrize("prove_exposure", (False, True))
def test_navigation_uses_existing_operation_with_terminal_native_driver_receipt(
    qtbot,
    native_snapshot_bridge,
    prove_exposure,
):
    from openhcs.agent.dto.ui_bridge import (
        UiWindowNavigateRequest,
        UiWindowNavigateResult,
    )
    from openhcs.pyqt_gui.services.ui_bridge_windows import (
        UiWindowProjectionService,
        WindowRouteIndex,
    )
    from pyqt_reactive.services.window_manager import WindowManager
    from pyqt_reactive.services.window_navigation import FieldWindowNavigationDriver

    bridge, form, _ = native_snapshot_bridge
    window = form.window()
    selected = []

    class NativeProofDriver(FieldWindowNavigationDriver):
        def target_exposed(self, request):
            if prove_exposure:
                return form.widgets["number"].isVisibleTo(window)
            return super().target_exposed(request)

    class ScopeOnlyProjection(UiWindowProjectionService):
        def _route_index(self):
            # Explicit source injection of an empty static graph; the production
            # dynamic route, deferred callback and DTO projection execute below.
            return WindowRouteIndex((), ())

    scope_id = "native-navigation-receipt"
    WindowManager.register(scope_id, window, NativeProofDriver(selected.append))
    bridge.register_window_provider(ScopeOnlyProjection(None))
    try:
        accepted = bridge.navigate_window(
            UiWindowNavigateRequest.from_fields(
                window_id=scope_id,
                field_path="number",
                create_if_missing=False,
            )
        )
        assert accepted.operation_id
        assert not accepted.navigated
        assert accepted.target_exposed is None
        qtbot.waitUntil(
            lambda: bridge.get_operation_status(accepted.operation_id).completed_at_unix
            is not None
        )
        operation = bridge.get_operation_status(accepted.operation_id)
        contract = UiBridgeOperationContractABC.for_name(
            operation.identity.operation_name
        )
        result = AgentDtoJsonCodec.dataclass_from_json(
            contract.response_type, operation.result_payload
        )
        assert isinstance(result, UiWindowNavigateResult)
        assert operation.status == "completed"
        assert selected == ["number"]
        assert result.navigated
        assert result.target_exposed is (True if prove_exposure else None)
        assert not result.errors
    finally:
        WindowManager.unregister(scope_id, window)


def test_unowned_target_navigation_is_terminal_failed_not_pending(
    native_snapshot_bridge,
):
    from openhcs.agent.dto.ui_bridge import UiWindowNavigateRequest

    bridge, _, window_id = native_snapshot_bridge
    accepted = bridge.navigate_window(
        UiWindowNavigateRequest.from_fields(
            window_id=window_id,
            field_path="unowned",
            create_if_missing=False,
        )
    )
    assert accepted.errors
    assert accepted.operation_id
    assert bridge.get_operation_status(accepted.operation_id).status == "failed"


def test_tracker_observation_failure_uses_declared_operation_error_owner(
    native_snapshot_bridge,
):
    from openhcs.agent.services.ui_bridge_service import UiBridgeNavigateWindowOperation

    bridge, _, _ = native_snapshot_bridge

    def rejected(completed):
        raise ValueError("native provider refused")

    with pytest.raises(ValueError, match="native provider refused"):
        bridge._operation_tracker.observe(
            UiBridgeNavigateWindowOperation, "target", rejected
        )
    operation = tuple(bridge._operation_tracker._operations.values())[-1]
    assert operation.status == "failed"
    assert (
        operation.errors[0].code == UiBridgeNavigateWindowOperation.failure_error_code
    )


def test_snapshot_tool_arguments_derive_capture_owner_fields(tmp_path):
    from python_introspect import project_dataclass
    from pyqt_reactive.services.window_snapshot import WindowSnapshotCaptureSpec

    request = UiWindowSnapshotRequest.from_fields(
        window_id="engineering-form",
        output_dir_path=str(tmp_path),
        capture_scope="window",
        frame_condition="no_flash",
        observation_timeout_s=2.5,
        create_if_missing=False,
    )
    assert request.as_tool_arguments() == {
        **to_jsonable(project_dataclass(WindowSnapshotCaptureSpec, request)),
        "window_id": "engineering-form",
        "create_if_missing": False,
    }
