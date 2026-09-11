"""Show the source-backed multiprocess desktop execution topology."""

from pathlib import Path

from matplotlib.patches import Rectangle

from build_slas_visual_story import BLUE, MUTED, ORANGE, PURPLE, TEAL, FigureSheet, ROOT


def processes():
    sheet = FigureSheet(
        "process_architecture", "Separate editing, execution and inspection", 7.3
    )
    for source in (
        "openhcs/runtime/zmq_execution_client.py",
        "openhcs/runtime/zmq_execution_server.py",
        "openhcs/runtime/zmq_worker_execution.py",
        "openhcs/core/orchestrator/worker_execution.py",
        "openhcs/core/steps/function_artifact_materialization.py",
        "openhcs/runtime/napari_viewer_server.py",
        "openhcs/runtime/fiji_viewer_server.py",
        "docs/source/architecture/zmq_execution_service_extracted.rst",
        "docs/source/architecture/streaming_boundary_and_wrappers.rst",
    ):
        sheet.source(ROOT / source)
    sheet.source(Path(__file__).resolve())

    sheet.text(4, 90, "Scientist and MCP agent", size=10, color=PURPLE)
    sheet.box(4, 66, 32, 21, "UI process",
              "GUI + Python editing\nMCP bridge · status display", color=PURPLE)
    sheet.box(62, 66, 34, 21, "ZMQ execution server",
              "Function catalog · compilation\nScheduling · execution status", color=BLUE)
    sheet.arrow((36, 81), (62, 81), color=BLUE)
    sheet.text(49, 83, "Compile / run requests", size=9, ha="center", color=BLUE)
    sheet.arrow((62, 71), (36, 71), color=BLUE)
    sheet.text(49, 73, "Status / progress", size=9, ha="center", color=BLUE)

    sheet.text(4, 54, "Worker processes", size=12, weight="bold", color=ORANGE)
    sheet.axis.add_patch(Rectangle(
        (2, 27), 58, 24, linewidth=1, linestyle="--",
        edgecolor=ORANGE, facecolor="#fffaf4", zorder=0,
    ))
    for x, label in ((4, "Worker 1"), (23, "Worker 2"), (42, "Worker N")):
        sheet.box(x, 31, 16, 17, label, "Steps + results\nCPU / GPU", color=ORANGE)
    sheet.arrow((70, 66), (60, 51), both=True, color=BLUE)
    sheet.text(44, 61, "Compiled work\nProgress / results", size=9, ha="center",
               va="center", color=BLUE, linespacing=1.5)

    sheet.text(74, 54, "Viewer processes", size=11, weight="bold", color=TEAL)
    sheet.box(74, 36, 22, 15, "napari", "Layers · ROI selection", color=TEAL)
    sheet.box(74, 18, 22, 15, "Fiji", "Images · ROI Manager", color=TEAL)
    sheet.route(((60, 39), (70, 39), (70, 43.5), (74, 43.5)), color=TEAL)
    sheet.route(((70, 39), (70, 25.5), (74, 25.5)), color=TEAL)
    sheet.text(66, 45, "Images\nROIs", size=9, ha="center", color=TEAL)

    sheet.box(4, 7, 54, 12, "Image sources and saved outputs",
              "Acquisition files · saved images, ROIs and tables", color=MUTED)
    sheet.arrow((31, 27), (31, 19), both=True, color=TEAL)
    sheet.text(21, 24, "Read / write", size=9, ha="center", color=TEAL)
    sheet.text(50, 3, "Multiprocess deployment • configurable worker and viewer counts",
               size=10, ha="center", color=MUTED)
    sheet.save()


if __name__ == "__main__":
    processes()
