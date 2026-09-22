"""Assemble the agent-authored neurite workflow and current native replay."""

from __future__ import annotations

import ast
import csv
import hashlib
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import tifffile
from skimage.segmentation import find_boundaries

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = Path(__file__).resolve().parent / "slas"
SOURCE_MANIFEST = OUTPUT / "figure3_current_replay_sources.json"
NEURITE_PIPELINE_SUFFIX = "/neurite/plate"
# Native screenshot coordinates: x0, y0, x1, y1 of the napari canvas.
DETAIL_CANVAS_XYXY = (580, 40, 1753, 720)
SOMA_ASSIGNMENT_PADDING = 72


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def normalize_generated_svg(path: Path) -> None:
    """Remove generator-only end-of-line whitespace from an SVG artifact."""

    text = path.read_text(encoding="utf-8")
    normalized = "\n".join(line.rstrip() for line in text.splitlines()) + "\n"
    path.write_text(normalized, encoding="utf-8")


def verified_sources() -> tuple[dict[str, object], dict[str, Path]]:
    manifest = json.loads(SOURCE_MANIFEST.read_text(encoding="utf-8"))
    paths: dict[str, Path] = {}
    for role, declaration in manifest["sources"].items():
        path = ROOT / declaration["path"]
        if digest(path) != declaration["sha256"]:
            raise ValueError(f"Figure 3 source hash differs for {role}: {path}")
        paths[role] = path
    return manifest, paths


def neurite_step_labels(path: Path) -> list[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    pipeline_data = next(
        node.value
        for node in tree.body
        if isinstance(node, ast.Assign)
        and any(
            isinstance(target, ast.Name) and target.id == "pipeline_data"
            for target in node.targets
        )
    )
    if not isinstance(pipeline_data, ast.Dict):
        raise ValueError("pipeline_data must be a literal dictionary")
    step_nodes = next(
        value.elts
        for key, value in zip(pipeline_data.keys, pipeline_data.values, strict=True)
        if isinstance(key, ast.Constant)
        and isinstance(key.value, str)
        and key.value.endswith(NEURITE_PIPELINE_SUFFIX)
        and isinstance(value, ast.List)
    )
    labels: list[str] = []
    for step in step_nodes:
        if not isinstance(step, ast.Call):
            raise ValueError("Neurite pipeline entries must be FunctionStep calls")
        keywords = {item.arg: item.value for item in step.keywords}
        name = ast.literal_eval(keywords["name"])
        function_node = keywords["func"]
        if isinstance(function_node, ast.Tuple):
            function_node = function_node.elts[0]
        labels.append(f"{name}\n{ast.unparse(function_node)}")
    if len(labels) != 2:
        raise ValueError("Figure 3 expects the frozen two-step neurite pipeline")
    return labels


def read_measurements(
    cell_path: Path,
    summary_path: Path,
) -> tuple[list[dict[str, str]], dict[str, str]]:
    with cell_path.open(newline="", encoding="utf-8") as stream:
        cells = list(csv.DictReader(stream))
    with summary_path.open(newline="", encoding="utf-8") as stream:
        summaries = list(csv.DictReader(stream))
    if len(summaries) != 1:
        raise ValueError("Figure 3 expects one retained summary row")
    summary = summaries[0]
    if int(summary["number_of_cells"]) != len(cells):
        raise ValueError("Summary cell count differs from the per-cell table")
    total_length = sum(float(row["total_outgrowth_um"]) for row in cells)
    if not np.isclose(total_length, float(summary["total_outgrowth_um"]), atol=1e-9):
        raise ValueError("Summary length differs from the per-cell table")
    if sum(int(row["processes"]) for row in cells) != int(summary["total_processes"]):
        raise ValueError("Summary process count differs from the per-cell table")
    if sum(int(row["branches"]) for row in cells) != int(summary["total_branches"]):
        raise ValueError("Summary branch count differs from the per-cell table")
    return cells, summary


def detail_canvas(path: Path) -> np.ndarray:
    pixels = plt.imread(path)
    left, top, right, bottom = DETAIL_CANVAS_XYXY
    if pixels.shape[1] < right or pixels.shape[0] < bottom:
        raise ValueError(f"Native detail capture geometry changed: {path}")
    return pixels[top:bottom, left:right]


def nonempty_label_plane(path: Path) -> np.ndarray:
    """Return the one spatial plane containing labels in a retained artifact."""

    labels = np.asarray(tifffile.imread(path))
    if labels.ndim == 2:
        return labels
    planes = labels.reshape((-1, *labels.shape[-2:]))
    nonempty = tuple(plane for plane in planes if np.any(plane))
    if len(nonempty) != 1:
        raise ValueError(
            f"Expected one nonempty label plane in {path}; found {len(nonempty)}"
        )
    return nonempty[0]


def overlapping_label(
    labels: np.ndarray,
    selection: np.ndarray,
    *,
    role: str,
) -> int:
    """Resolve one retained label identity from maximal spatial overlap."""

    identities, counts = np.unique(labels[selection], return_counts=True)
    candidates = tuple(
        (int(identity), int(count))
        for identity, count in zip(identities, counts, strict=True)
        if identity != 0
    )
    if not candidates:
        raise ValueError(f"Selected soma has no overlapping {role} label")
    maximum = max(count for _, count in candidates)
    winners = tuple(identity for identity, count in candidates if count == maximum)
    if len(winners) != 1:
        raise ValueError(f"Selected soma has ambiguous {role} labels: {winners}")
    return winners[0]


def soma_assignment_overlay(
    neurite_signal: np.ndarray,
    nuclei_labels: np.ndarray,
    cell_body_labels: np.ndarray,
    neuron_labels: np.ndarray,
) -> tuple[np.ndarray, dict[str, object]]:
    """Render one derived nucleus-to-soma-to-neuron ownership example."""

    body_identities = tuple(
        int(value) for value in np.unique(cell_body_labels) if value
    )
    if not body_identities:
        raise ValueError("Retained replay contains no cell-body labels")
    body_centroid_y = {
        identity: float(np.nonzero(cell_body_labels == identity)[0].mean())
        for identity in body_identities
    }
    target_body = max(body_identities, key=body_centroid_y.__getitem__)
    body_mask = cell_body_labels == target_body
    target_nucleus = overlapping_label(
        nuclei_labels,
        body_mask,
        role="nucleus",
    )
    target_neuron = overlapping_label(
        neuron_labels,
        body_mask,
        role="neuron",
    )
    nucleus_mask = nuclei_labels == target_nucleus
    neuron_mask = neuron_labels == target_neuron

    rows, columns = np.nonzero(body_mask | nucleus_mask)
    top = max(0, int(rows.min()) - SOMA_ASSIGNMENT_PADDING)
    bottom = min(neurite_signal.shape[0], int(rows.max()) + SOMA_ASSIGNMENT_PADDING + 1)
    left = max(0, int(columns.min()) - SOMA_ASSIGNMENT_PADDING)
    right = min(
        neurite_signal.shape[1], int(columns.max()) + SOMA_ASSIGNMENT_PADDING + 1
    )
    crop = np.s_[top:bottom, left:right]

    grayscale = neurite_signal[crop].astype(np.float32) / 255.0
    overlay = np.repeat(grayscale[..., np.newaxis], 3, axis=-1)
    cropped_body = body_mask[crop]
    cropped_nucleus = nucleus_mask[crop]
    cropped_neuron = neuron_mask[crop]
    overlay[cropped_body] = 0.55 * overlay[cropped_body] + 0.45 * np.array(
        [0.0, 0.85, 0.95]
    )
    overlay[cropped_nucleus] = 0.45 * overlay[cropped_nucleus] + 0.55 * np.array(
        [1.0, 0.15, 0.55]
    )
    overlay[find_boundaries(cropped_neuron, mode="outer")] = (1.0, 0.78, 0.0)
    overlay[find_boundaries(cropped_body, mode="outer")] = (0.0, 0.95, 1.0)
    overlay[find_boundaries(cropped_nucleus, mode="outer")] = (1.0, 0.15, 0.55)
    return overlay, {
        "cell_body_label": target_body,
        "nucleus_label": target_nucleus,
        "neuron_label": target_neuron,
        "crop_xyxy": [left, top, right, bottom],
        "selection": "cell body with greatest image-row centroid",
        "label_matching": "maximal nonzero pixel overlap with selected cell body",
        "colors": {
            "nucleus": "magenta",
            "cell_body": "cyan",
            "assigned_neuron": "yellow",
        },
    }


def build() -> None:
    manifest, sources = verified_sources()
    images = [
        ("Neurite and soma signal", tifffile.imread(sources["input_neurite"])),
        ("Nuclear signal", tifffile.imread(sources["input_nuclear"])),
    ]
    if any(
        pixels.shape != (800, 800) or pixels.dtype != np.uint8 for _, pixels in images
    ):
        raise ValueError("Figure 3 input geometry or dtype changed")
    step_labels = neurite_step_labels(sources["pipeline_source"])
    cells, summary = read_measurements(
        sources["cell_measurements"],
        sources["summary_measurements"],
    )
    overview = plt.imread(sources["viewer_overview"])
    crossing_detail = detail_canvas(sources["crossing_detail"])
    nuclei_labels = nonempty_label_plane(sources["nuclei_labels"])
    cell_body_labels = nonempty_label_plane(sources["cell_body_labels"])
    neuron_labels = nonempty_label_plane(sources["neuron_labels"])
    soma_detail, soma_overlay_receipt = soma_assignment_overlay(
        images[0][1],
        nuclei_labels,
        cell_body_labels,
        neuron_labels,
    )
    nuclei_count = int(np.count_nonzero(np.unique(nuclei_labels)))

    OUTPUT.mkdir(parents=True, exist_ok=True)
    figure = plt.figure(figsize=(9, 9.2), layout="constrained")
    grid = figure.add_gridspec(
        5,
        6,
        height_ratios=(1.0, 0.2, 1.1, 0.9, 0.8),
    )
    for index, (title, pixels) in enumerate(images):
        axis = figure.add_subplot(grid[0, index * 3 : (index + 1) * 3])
        axis.imshow(pixels, cmap="gray", vmin=0, vmax=255, interpolation="nearest")
        axis.set_title(f"{'AB'[index]}  {title}", fontsize=12)
        axis.set_axis_off()

    for index, label in enumerate(step_labels):
        axis = figure.add_subplot(grid[1, index * 3 : (index + 1) * 3])
        axis.text(
            0.5,
            0.5,
            f"Step {index + 1}: {label}",
            fontsize=9.5,
            color="#16877f",
            ha="center",
            va="center",
            bbox={
                "boxstyle": "round,pad=0.55",
                "facecolor": "#edf7f5",
                "edgecolor": "#16877f",
            },
        )
        axis.set_axis_off()

    overview_axis = figure.add_subplot(grid[2:4, :4])
    overview_axis.imshow(overview, interpolation="nearest")
    overview_axis.set_title("C  Current-source napari review", fontsize=12)
    overview_axis.set_axis_off()

    for position, title, pixels in (
        (grid[2, 4:], "D  Nucleus-supported soma", soma_detail),
        (grid[3, 4:], "E  Resolved crossing", crossing_detail),
    ):
        axis = figure.add_subplot(position)
        axis.imshow(pixels, interpolation="nearest")
        axis.set_title(title, fontsize=10.5)
        axis.set_axis_off()

    lengths_axis = figure.add_subplot(grid[4, :4])
    cell_ids = [int(row["cell"]) for row in cells]
    lengths = [float(row["total_outgrowth_um"]) for row in cells]
    lengths_axis.bar(cell_ids, lengths, color="#16877f", width=0.72)
    lengths_axis.set_title("F  Measured path length by neuron", fontsize=11)
    lengths_axis.set_xlabel("Neuron identity")
    lengths_axis.set_ylabel("Path length (pixels)")
    lengths_axis.set_xticks(cell_ids)
    lengths_axis.spines[["top", "right"]].set_visible(False)
    lengths_axis.grid(axis="y", color="#d9e0e5", linewidth=0.7)
    lengths_axis.set_axisbelow(True)

    summary_axis = figure.add_subplot(grid[4, 4:])
    summary_axis.set_title("G  Current replay", fontsize=11)
    summary_rows = (
        ("Neurons", int(summary["number_of_cells"])),
        ("Nuclei", nuclei_count),
        ("Processes", int(summary["total_processes"])),
        ("Branch events", int(summary["total_branches"])),
        ("Resolved crossovers", int(summary["resolved_crossovers"])),
        ("Total path", f"{float(summary['total_outgrowth_um']):.1f} px"),
    )
    table = summary_axis.table(
        cellText=summary_rows,
        colWidths=(0.68, 0.32),
        cellLoc="left",
        loc="center",
    )
    table.auto_set_font_size(False)
    table.set_fontsize(9)
    table.scale(1.0, 1.35)
    for (row, column), cell in table.get_celld().items():
        cell.set_edgecolor("#d9e0e5")
        cell.set_facecolor("#edf7f5" if row % 2 == 0 else "white")
        if column == 1:
            cell.get_text().set_ha("right")
    summary_axis.set_axis_off()

    outputs: list[Path] = []
    for suffix in ("png", "pdf", "svg"):
        destination = OUTPUT / f"figure3_agent_workflow.{suffix}"
        figure.savefig(destination, dpi=300)
        if suffix == "svg":
            normalize_generated_svg(destination)
        outputs.append(destination)
    plt.close(figure)

    receipt = {
        "source_manifest": str(SOURCE_MANIFEST.relative_to(ROOT)),
        "source_manifest_sha256": digest(SOURCE_MANIFEST),
        "source_sha256": {
            str(path.relative_to(ROOT)): digest(path) for path in sources.values()
        },
        "generator_sha256": digest(Path(__file__)),
        "replay_execution_id": manifest["replay_execution_id"],
        "image_display": "Original uint8 TIFF pixels displayed linearly at 0..255",
        "viewer_display": (
            "Panel C and the crossing detail are native Qt captures; the crossing "
            f"detail is an unchanged canvas crop using xyxy={DETAIL_CANVAS_XYXY}. "
            "Panel D is a deterministic overlay of retained input pixels and labels."
        ),
        "soma_assignment_overlay": soma_overlay_receipt,
        "measurement_units": (
            "Pixels: the retained source has unit spacing and no physical calibration"
        ),
        "step_labels": step_labels,
        "derived_summary": {label: value for label, value in summary_rows},
        "output_sha256": {path.name: digest(path) for path in outputs},
    }
    (OUTPUT / "figure3_provenance.json").write_text(
        json.dumps(receipt, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Rendered current-replay agent figure to {OUTPUT}")


if __name__ == "__main__":
    build()
