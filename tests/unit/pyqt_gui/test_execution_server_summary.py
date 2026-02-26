from openhcs.pyqt_gui.widgets.shared.server_browser import (
    ProgressNode,
    summarize_execution_server,
)


def test_execution_server_summary_handles_empty_nodes():
    summary = summarize_execution_server([])
    assert summary.status_text == "✅ Idle"
    assert summary.info_text == ""


def test_execution_server_summary_formats_counts_and_average():
    nodes = [
        ProgressNode(
            node_id="p1",
            node_type="plate",
            label="p1",
            status="⏳ Queued",
            info="",
            percent=0.0,
        ),
        ProgressNode(
            node_id="p2",
            node_type="plate",
            label="p2",
            status="⚙️ Executing",
            info="",
            percent=50.0,
        ),
        ProgressNode(
            node_id="p3",
            node_type="plate",
            label="p3",
            status="✅ Complete",
            info="",
            percent=100.0,
        ),
    ]

    summary = summarize_execution_server(nodes)

    assert "⏳ 1 queued" in summary.status_text
    assert "⚙️ 1 executing" in summary.status_text
    assert "✅ 1 complete" in summary.status_text
    assert summary.info_text == "Avg: 50.0% | 3 plates"


def test_execution_server_summary_includes_failed_count():
    nodes = [
        ProgressNode(
            node_id="p1",
            node_type="plate",
            label="p1",
            status="❌ Failed",
            info="",
            percent=25.0,
        )
    ]

    summary = summarize_execution_server(nodes)

    assert "❌ 1 failed" in summary.status_text
    assert summary.info_text == "Avg: 25.0% | 1 plates"
