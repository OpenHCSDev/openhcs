"""Show the source-backed multiprocess desktop execution topology."""

from pathlib import Path

from matplotlib.patches import Rectangle

from build_slas_visual_story import BLUE, INK, MUTED, ORANGE, PURPLE, TEAL, FigureSheet, ROOT


def processes(*, stem="process_architecture", with_logos=False):
    sheet = FigureSheet(stem, "Separate editing, execution and inspection", 5.1)
    # The manuscript places this at 6.5 inches: a narrower native canvas keeps
    # the existing type hierarchy readable without enlarging every label by hand.
    sheet.figure.set_size_inches(7, 5.1)
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
    ui_right = 43
    if with_logos:
        logos = ROOT / "website/assets/logos"
        sheet.source(logos / "README.md")
        sheet.axis.add_patch(Rectangle((4, 66), ui_right - 4, 21,
                                      edgecolor=PURPLE, facecolor="white", linewidth=1.15))
        sheet.text(23.5, 83, "UI process · shared workflow", size=11,
                   weight="bold", ha="center", color=PURPLE)
        sheet.axis.add_patch(Rectangle((6, 75), 6, 6, edgecolor=PURPLE, facecolor="white"))
        for y in (76, 78, 80):
            sheet.axis.plot((7, 11), (y, y), color=PURPLE, linewidth=1)
        for name, x in (("python.svg", 15), ("mcp.svg", 24), ("cellprofiler.png", 33)):
            sheet.asset(logos / name, (x, 75, 6, 6))
        for x, label in ((9, "Forms"), (18, "Python"), (27, "MCP"), (36, "Import")):
            sheet.text(x, 72.8, label, size=9, ha="center")
        sheet.text(23.5, 68.5, "One editable pipeline · status", size=9, ha="center")
    else:
        sheet.box(4, 66, ui_right - 4, 21, "UI process",
                  "GUI + Python editing\nMCP bridge · status display", color=PURPLE)
    sheet.box(64, 66, 32, 21, "ZMQ execution server",
              "Function catalog · compilation\nScheduling · execution status", color=BLUE)
    request_midpoint = (ui_right + 64) / 2
    sheet.arrow((ui_right, 81), (64, 81), color=BLUE)
    sheet.text(request_midpoint, 83, "Compile / run", size=9, ha="center", color=BLUE)
    sheet.arrow((64, 71), (ui_right, 71), color=BLUE)
    sheet.text(request_midpoint, 73, "Status / progress", size=9, ha="center", color=BLUE)

    sheet.text(4, 60, "Worker processes", size=12, weight="bold", color=ORANGE)
    sheet.axis.add_patch(Rectangle((2, 31), 58, 26, linewidth=1, linestyle="--",
                                  edgecolor=ORANGE, facecolor="#fffaf4", zorder=0))
    for x, label in ((4, "Worker 1"), (23, "Worker 2"), (42, "Worker N")):
        sheet.box(x, 43, 16, 12, label, "Processing steps\nCPU / GPU", color=ORANGE)
    if with_logos:
        # These marks identify the six array libraries used by ArrayBridge;
        # the runtime declarations, not the diagram, determine CPU/GPU support.
        for name, label, x in (
            ("numpy.svg", "NumPy", 4),
            ("cupy.svg", "CuPy", 13.5),
            ("pytorch.svg", "PyTorch", 23),
            ("tensorflow.svg", "TensorFlow", 32.5),
            ("jax.png", "JAX", 42),
            ("pyclesperanto.png", "pyclesperanto", 49.8),
        ):
            sheet.asset(logos / name, (x, 34.5, 7, 7))
            sheet.text(x + 3.5, 32.5, label, size=8.5, ha="center")
        # The retained TensorFlow asset is the official white-on-dark variant.
        sheet.axis.add_patch(Rectangle((32.5, 34.5), 7, 7,
                                      facecolor=INK, edgecolor="none", zorder=2))
    sheet.arrow((71, 66), (60, 57), both=True, color=BLUE)
    sheet.text(49, 62, "Work / results", size=9, ha="center", color=BLUE)

    sheet.text(75, 60, "Viewer processes", size=11, weight="bold", color=TEAL)
    sheet.box(74, 44, 22, 13, "napari", "Layers · ROIs", color=TEAL)
    sheet.box(74, 27, 22, 13, "Fiji", "Images · ROIs", color=TEAL)
    if with_logos:
        sheet.asset(logos / "napari.svg", (75, 50, 4.5, 5.5))
        sheet.asset(logos / "fiji.svg", (75, 33, 4.5, 5.5))
    sheet.route(((60, 44), (69, 44), (69, 50.5), (74, 50.5)), color=TEAL)
    sheet.route(((69, 44), (69, 33.5), (74, 33.5)), color=TEAL)
    sheet.text(66.5, 52, "Images\nROIs", size=9, ha="center", color=TEAL)

    sheet.axis.add_patch(Rectangle((4, 3), 54, 21, linewidth=1.15,
                                  edgecolor=MUTED, facecolor="white", zorder=2))
    sheet.text(31, 20, "Image sources and saved outputs", size=11,
               weight="bold", ha="center", color=MUTED)
    sheet.text(31, 16, "Images · ROIs · measurements", size=9, ha="center")
    sheet.arrow((31, 31), (31, 24), both=True, color=TEAL)
    sheet.text(20, 27, "Read / write", size=9, ha="center", color=TEAL)
    if with_logos:
        sheet.asset(logos / "bioformats.svg", (7, 6, 9, 8))
        sheet.asset(logos / "zarr.svg", (20, 6, 14, 8), trim=True)
        sheet.text(11.5, 4.5, "Bio-Formats", size=9, ha="center")
        sheet.text(27, 4.5, "OME-Zarr", size=9, ha="center")
        sheet.text(45, 10, "Image folders\nOMERO\n(experimental)", size=9,
                   ha="center", va="center", color=MUTED)
    else:
        sheet.text(31, 9, "Image folders · Zarr\nOMERO (experimental)", size=9,
                   ha="center", color=MUTED)
    sheet.save()


if __name__ == "__main__":
    processes()
