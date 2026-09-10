"""Native bridge actions consume generic row-disclosure declarations."""

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


def test_bridge_toggle_is_row_local_and_auto_still_selects(qtbot):
    view = ReorderableListWidget()
    qtbot.addWidget(view)
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
    target = WindowProjectionTarget(
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
    projection = WidgetTreeProjectionService.project(view)

    def walk(node):
        yield node
        for child in node.children:
            yield from walk(child)

    row_descriptor = next(
        node for node in walk(projection.root) if node.class_name == "QModelIndex"
    )
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
