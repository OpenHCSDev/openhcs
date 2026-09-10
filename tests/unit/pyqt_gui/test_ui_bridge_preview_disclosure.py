"""Native bridge actions consume generic row-disclosure declarations."""

import pytest
from PyQt6 import sip
from PyQt6.QtCore import QCoreApplication, QEvent, Qt
from PyQt6.QtGui import QColor
from PyQt6.QtWidgets import QListWidgetItem

from pyqt_reactive.core import ReorderableListWidget
from pyqt_reactive.services.widget_tree_projection import (
    WidgetTreeProjectionService,
    WidgetActionKind,
)
from pyqt_reactive.widgets.shared.list_item_delegate import (
    LAYOUT_ROLE,
    PREVIEW_WRAP_ROLE,
    MultilinePreviewItemDelegate,
    PreviewWrapMode,
)
from pyqt_reactive.widgets.shared.styled_text_layout import StyledTextLayout, Segment

from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.ui_bridge import (
    UiWindowSummary,
    UiWindowIdentity,
    UiWidgetActionInvokeRequest,
)
from openhcs.pyqt_gui.services.ui_bridge_windows import (
    WindowProjectionTarget,
    UiWidgetActionInvokeResultFactory,
)


@pytest.fixture
def preview_target(qapp):
    view = ReorderableListWidget()
    view.setItemDelegate(
        MultilinePreviewItemDelegate(
            QColor("black"), QColor("gray"), QColor("white"), parent=view
        )
    )
    view.resize(400, 400)
    for name in ("First plate", "Second plate"):
        row = QListWidgetItem(name)
        row.setData(
            LAYOUT_ROLE,
            StyledTextLayout(
                name=Segment(name),
                preview_segments=[Segment("source=" + "/images/" * 30)],
                multiline=True,
            ),
        )
        view.addItem(row)
    view.show()
    view.doItemsLayout()
    yield WindowProjectionTarget(
        view,
        UiWindowSummary(
            schema_version=SCHEMA_VERSION,
            identity=UiWindowIdentity(window_id="preview-test"),
            title="Preview test",
            window_kind="widget",
            visible=True,
            focusable=True,
        ),
    )
    if not sip.isdeleted(view):
        view.close()
        view.deleteLater()


def _first_row_descriptor(view):
    projection = WidgetTreeProjectionService.project(view)

    def walk(node):
        yield node
        for child in node.children:
            yield from walk(child)

    return next(
        node for node in walk(projection.root) if node.class_name == "QModelIndex"
    )


def test_bridge_toggle_is_row_local_and_auto_still_selects(qtbot, preview_target):
    target = preview_target
    view = target.widget
    row_descriptor = _first_row_descriptor(view)
    factory = UiWidgetActionInvokeResultFactory()
    request = UiWidgetActionInvokeRequest.from_fields(
        window_id="preview-test",
        path_id=row_descriptor.path_id,
        action_kind=WidgetActionKind.ITEM_PREVIEW_TOGGLE.value,
    )
    result = factory.invoke(request, target)
    assert not result.errors
    assert result.invoked
    qtbot.waitUntil(
        lambda: view.item(0).data(PREVIEW_WRAP_ROLE) is PreviewWrapMode.WRAPPED
    )
    assert view.item(1).data(PREVIEW_WRAP_ROLE) is None
    # Require a real selection transition, not the initially selected first row.
    # The bridge schedules the action, so its accepted receipt is not completion.
    view.setCurrentRow(1)
    auto_request = UiWidgetActionInvokeRequest.from_fields(
        window_id="preview-test",
        path_id=row_descriptor.path_id,
        action_kind="auto",
    )
    selected = factory.invoke(auto_request, target)
    assert selected.action_kind == WidgetActionKind.ITEM_SELECT.value
    qtbot.waitUntil(lambda: view.currentRow() == 0)
    assert view.item(0).data(PREVIEW_WRAP_ROLE) is PreviewWrapMode.WRAPPED


@pytest.mark.parametrize(
    "action_kind",
    [WidgetActionKind.ITEM_SELECT, WidgetActionKind.ITEM_PREVIEW_TOGGLE],
)
def test_closing_view_cancels_accepted_row_action(qtbot, preview_target, action_kind):
    view = preview_target.widget
    view.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
    request = UiWidgetActionInvokeRequest.from_fields(
        window_id="preview-test",
        path_id=_first_row_descriptor(view).path_id,
        action_kind=action_kind.value,
    )
    result = UiWidgetActionInvokeResultFactory().invoke(request, preview_target)
    assert result.invoked
    assert not result.errors

    view.close()
    # Deliver the real close's deferred deletion before the accepted zero-timer.
    QCoreApplication.sendPostedEvents(None, QEvent.Type.DeferredDelete)
    assert sip.isdeleted(view)
    with qtbot.captureExceptions() as exceptions:
        QCoreApplication.processEvents()
    assert not exceptions


@pytest.mark.parametrize(
    "action_kind",
    [WidgetActionKind.ITEM_SELECT, WidgetActionKind.ITEM_PREVIEW_TOGGLE],
)
def test_removing_row_cancels_accepted_action(qtbot, preview_target, action_kind):
    view = preview_target.widget
    request = UiWidgetActionInvokeRequest.from_fields(
        window_id="preview-test",
        path_id=_first_row_descriptor(view).path_id,
        action_kind=action_kind.value,
    )
    result = UiWidgetActionInvokeResultFactory().invoke(request, preview_target)
    assert result.invoked
    removed = view.takeItem(0)
    assert removed.text() == "First plate"
    view.setCurrentRow(-1)
    with qtbot.captureExceptions() as exceptions:
        QCoreApplication.processEvents()
    assert not exceptions
    assert view.currentRow() == -1
    assert view.item(0).data(PREVIEW_WRAP_ROLE) is None


@pytest.mark.parametrize(
    "action_kind",
    [WidgetActionKind.ITEM_SELECT, WidgetActionKind.ITEM_PREVIEW_TOGGLE],
)
def test_queued_action_tracks_original_row_after_insertion(
    qtbot, preview_target, action_kind
):
    view = preview_target.widget
    original = view.item(0)
    request = UiWidgetActionInvokeRequest.from_fields(
        window_id="preview-test",
        path_id=_first_row_descriptor(view).path_id,
        action_kind=action_kind.value,
    )
    result = UiWidgetActionInvokeResultFactory().invoke(request, preview_target)
    assert result.invoked
    view.insertItem(0, QListWidgetItem("New plate"))
    view.setCurrentRow(-1)
    with qtbot.captureExceptions() as exceptions:
        QCoreApplication.processEvents()
    assert not exceptions
    assert view.item(1) is original
    if action_kind is WidgetActionKind.ITEM_SELECT:
        assert view.currentItem() is original
    else:
        assert original.data(PREVIEW_WRAP_ROLE) is PreviewWrapMode.WRAPPED
    assert view.item(0).data(PREVIEW_WRAP_ROLE) is None
