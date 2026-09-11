"""Assemble original inputs and a frame from the retained unattended run."""

from __future__ import annotations

import ast
import hashlib
import json
import subprocess
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
import tifffile


ROOT = Path(__file__).resolve().parents[2]
ASSETS = ROOT / "website/assets/agent"
OUTPUT = Path(__file__).resolve().parent / "slas"
FRAME_SECONDS = 600
# Editorial selections in the verified 1280 x 720 archived video frame.
# Coordinates are (left, top, right, bottom), without image resampling.
FRAME_DETAILS = (
    ("D  Neuron and neurite outlines", (380, 70, 725, 400)),
    ("E  Native measurement-table detail", (680, 500, 1155, 615)),
)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def build() -> None:
    record_path = ASSETS / "cold-start-workflow-record.json"
    record = json.loads(record_path.read_text())
    media = record["evidence"]["media"]
    video = ASSETS / media["uncut_video_path"]
    if digest(video) != media["uncut_video_sha256"]:
        raise ValueError("Original uncut video hash differs from run record")
    fixture = record["fixture"]
    images = []
    sources = {str(record_path.relative_to(ROOT)): digest(record_path), str(video.relative_to(ROOT)): digest(video)}
    for item in fixture["file_manifest"]:
        if Path(item["path"]).suffix != ".tif":
            continue
        path = Path(fixture["plate_root"]) / item["path"]
        if digest(path) != item["sha256"]:
            raise ValueError(f"Input hash differs from run record: {path}")
        pixels = tifffile.imread(path)
        if list(pixels.shape) != item["shape"] or str(pixels.dtype) != item["dtype"]:
            raise ValueError(f"Input geometry differs from run record: {path}")
        sources[str(path.relative_to(ROOT))] = digest(path)
        images.append((item["path"], pixels))
    if len(images) != 2:
        raise ValueError("This figure requires the recorded pair of input channels")
    OUTPUT.mkdir(parents=True, exist_ok=True)
    frame = OUTPUT / "figure3_original_video_frame.png"
    subprocess.run([
        "ffmpeg", "-v", "error", "-y", "-ss", str(FRAME_SECONDS),
        "-i", str(video), "-frames:v", "1", str(frame),
    ], check=True)
    pipeline = ASSETS / record["evidence"]["pipeline_source_path"]
    if digest(pipeline) != record["evidence"]["pipeline_source_sha256"]:
        raise ValueError("Saved pipeline differs from original run record")
    sources[str(pipeline.relative_to(ROOT))] = digest(pipeline)
    tree = ast.parse(pipeline.read_text())
    steps = [node for node in ast.walk(tree) if isinstance(node, ast.Call)
             and isinstance(node.func, ast.Name) and node.func.id == "FunctionStep"]
    step_labels = []
    for step in steps:
        keywords = {item.arg: item.value for item in step.keywords}
        name = ast.literal_eval(keywords["name"])
        function = ast.unparse(keywords["func"].elts[0])
        step_labels.append(f"{name}\n{function}")
    if len(step_labels) != 2:
        raise ValueError("Review the diagram when the retained step sequence changes")
    video_pixels = plt.imread(frame)
    if video_pixels.shape[:2] != (720, 1280):
        raise ValueError("Review editorial crops when original video geometry changes")
    fig = plt.figure(figsize=(9, 9.3), layout="constrained")
    grid = fig.add_gridspec(4, 2, height_ratios=(1, 0.24, 1.15, 0.8))
    for index, (name, pixels) in enumerate(images):
        axis = fig.add_subplot(grid[0, index])
        axis.imshow(pixels, cmap="gray", vmin=0, vmax=255, interpolation="nearest")
        axis.set_title(f"{'AB'[index]}  Original input: {name}", fontsize=12)
        axis.set_axis_off()
    for index, label in enumerate(step_labels):
        axis = fig.add_subplot(grid[1, index])
        axis.text(0.5, 0.5, label, fontsize=10, color="#16877f", ha="center", va="center",
                  bbox={"boxstyle": "round,pad=0.6", "facecolor": "#edf7f5", "edgecolor": "#16877f"})
        axis.set_axis_off()
    axis = fig.add_subplot(grid[2, :])
    axis.imshow(video_pixels)
    axis.set_title("C  Agent-authored steps and recorded napari inspection", fontsize=12)
    axis.set_axis_off()
    for index, (title, (left, top, right, bottom)) in enumerate(FRAME_DETAILS):
        axis.add_patch(Rectangle((left, top), right - left, bottom - top,
                                 fill=False, edgecolor="#f3ac44", linewidth=1))
        axis.text(left, top - 6, title[0], color="#f3ac44", fontsize=10)
        detail = fig.add_subplot(grid[3, index])
        detail.imshow(video_pixels[top:bottom, left:right], interpolation="nearest")
        detail.set_title(title, fontsize=11)
        detail.set_axis_off()
    outputs = [frame]
    for suffix in ("png", "pdf", "svg"):
        destination = OUTPUT / f"figure3_agent_workflow.{suffix}"
        fig.savefig(destination, dpi=300)
        outputs.append(destination)
    plt.close(fig)
    receipt = {
        "source_sha256": sources,
        "generator_sha256": digest(Path(__file__)),
        "run_id": record["run"]["run_id"],
        "openhcs_version": record["openhcs"]["version"],
        "video_frame_seconds": FRAME_SECONDS,
        "image_display": "Original uint8 TIFF pixels displayed linearly at 0..255; no spatial crop",
        "video_display": "Full original frame with labelled detail rectangles; D/E are unchanged pixel crops of the same frame, not the later corrected replay",
        "video_detail_crops_xyxy": {title: list(bounds) for title, bounds in FRAME_DETAILS},
        "step_labels": step_labels,
        "output_sha256": {p.name: digest(p) for p in outputs},
    }
    (OUTPUT / "figure3_provenance.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Rendered original-run agent figure to {OUTPUT}")


if __name__ == "__main__":
    build()
