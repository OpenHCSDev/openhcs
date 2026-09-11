"""Explain output handling with linked retained public neurite-analysis results.

The scientific panel reads existing TIFF, ROI and CSV files. It neither runs an
analysis nor changes results. The selection is an editorial replot, not a new UI
capture. Pipeline declarations verify how the object and measurement IDs relate.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path
from zipfile import ZipFile

import numpy as np
from roifile import ImagejRoi
import tifffile

from openhcs.core.artifacts import ObjectArtifactSubjectBinding
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    NEURITE_CELLS_OUTPUT, NEURITE_MORPHOLOGY_OUTPUT, UNIFIED_NEURONS_OUTPUT,
)
from polystore.roi import load_roi_zip_metadata
from build_slas_visual_story import (
    BLUE, MUTED, ORANGE, PALE, PURPLE, TEAL, FigureSheet, ROOT, OUTPUT, digest,
)


RESULTS = ROOT / "mcp_outputs/website-agent-demo/candidate-20260804-13/outputs/plate_openhcs"
SELECTED_NEURON = 2


def binding_for(spec):
    binding, = tuple(binding for relation in spec.relations
                     if (binding := relation.object_subject_binding()) is not None)
    return binding


def read_shapes(path):
    with ZipFile(path) as archive:
        metadata = load_roi_zip_metadata(archive)
        return tuple((name, info, ImagejRoi.frombytes(archive.read(name)).coordinates())
                     for name, info in metadata.items())


def build():
    record_path = ROOT / "website/assets/agent/cold-start-workflow-record.json"
    record = json.loads(record_path.read_text())
    corrected = record["evidence"]["post_qa_corrected_recapture"]
    image_path = RESULTS / "review_images/1_s001_w1_z001_t001.tif"
    roi_path = RESULTS / "images_results/1_s001_w1_z001_t001_neurons_step1_rois.roi.zip"
    graph_path = RESULTS / "images_results/1_s001_w1_z001_t001_neurite_morphology_step1.graph.roi.zip"
    table_path = RESULTS / "images_results/1_site-1_z_index-1_timepoint-1_neurite_outgrowth_cells_step1_details.csv"
    image = tifffile.imread(image_path)
    with table_path.open(newline="") as stream:
        rows = tuple(csv.DictReader(stream))
    shapes = read_shapes(roi_path)
    graph_shapes = read_shapes(graph_path)
    if image.shape != (800, 800) or image.dtype != np.uint8:
        raise ValueError("Review image dimensions/display after source change")
    roi_binding = binding_for(UNIFIED_NEURONS_OUTPUT)
    table_binding = binding_for(NEURITE_CELLS_OUTPUT)
    graph_binding = binding_for(NEURITE_MORPHOLOGY_OUTPUT)
    if not roi_binding.source == table_binding.source == graph_binding.source:
        raise ValueError("The displayed outputs no longer share one declared object source")
    subject_key = ObjectArtifactSubjectBinding.SUBJECT_FEATURE
    subject_id_key = ObjectArtifactSubjectBinding.SUBJECT_ID_FEATURE
    tokens = {info[subject_key] for _, info, _ in (*shapes, *graph_shapes)}
    token, = tokens
    source_identity = json.loads(token)
    if source_identity[2] != UNIFIED_NEURONS_OUTPUT.name:
        raise ValueError("Archived object subject differs from declared output")
    row_ids = {int(row[table_binding.id_field]) for row in rows}
    roi_ids = {info[subject_id_key] for _, info, _ in shapes}
    graph_ids = {info[subject_id_key] for _, info, _ in graph_shapes}
    if row_ids != roi_ids or not graph_ids <= row_ids or SELECTED_NEURON not in graph_ids:
        raise ValueError("Saved rows, shapes and graph paths do not have matching neuron IDs")
    for _, info, coordinates in shapes:
        if tuple(info["source_spatial_shape_yx"]) != image.shape:
            raise ValueError("ROI source image geometry differs from saved image")
        if not np.all((coordinates >= -.5) & (coordinates <= 799.5)):
            raise ValueError("ROI coordinates lie outside the declared image")
    summary = corrected["result_summary"]
    if (len(row_ids) != summary["neurons"]
            or sum(float(row["total_outgrowth_um"]) for row in rows) != summary["total_outgrowth_pixels"]
            or sum(int(row["branches"]) for row in rows) != summary["branches"]
            or len(graph_shapes) != summary["spatial_graph_path_count"]):
        raise ValueError("Archived result counts differ from the corrected public recapture")

    sheet = FigureSheet("outputs_and_inspection", "Keep images, objects and measurements connected", 9.2)
    for path in (
        record_path, image_path, roi_path, graph_path, table_path, Path(__file__),
        ROOT / "openhcs/core/artifacts.py",
        ROOT / "openhcs/core/runtime_measurements.py",
        ROOT / "openhcs/core/measurement_row_materialization.py",
        ROOT / "openhcs/core/pipeline/artifact_planning.py",
        ROOT / "openhcs/core/steps/function_artifact_materialization.py",
        ROOT / "openhcs/processing/materialization/options.py",
        ROOT / "openhcs/processing/materialization/core.py",
        ROOT / "openhcs/processing/backends/analysis/neurite_outgrowth.py",
        ROOT / "openhcs/runtime/napari_streaming_handlers.py",
        ROOT / "openhcs/runtime/napari_viewer_server.py",
        ROOT / "openhcs/napari_roi_manager/widgets/_roi_manager.py",
        ROOT / "external/PolyStore/src/polystore/roi.py",
        ROOT / "external/PolyStore/src/polystore/roi_converters.py",
        ROOT / "external/PolyStore/src/polystore/streaming/handlers/fiji_rois.py",
    ):
        sheet.source(path)

    sheet.panel("A", "Choose how to use the outputs of a function", 3, 91)
    sheet.box(25, 80, 50, 7, "Named results", "available to later processing steps", color=TEAL)
    for x, title, detail, color in (
        (5, "Images", "pixel arrays", BLUE),
        (37, "Objects", "labels + object IDs", PURPLE),
        (69, "Measurements", "values + object IDs", ORANGE),
    ):
        sheet.box(x, 68, 26, 7, title, detail, color=color)
        sheet.arrow((50, 80), (x + 13, 75), color=color)
        sheet.axis.plot([x + 13, x + 13], [68, 64], color=MUTED, linewidth=1.3)
    sheet.axis.plot([18, 82], [64, 64], color=MUTED, linewidth=1.3)
    sheet.arrow((27, 64), (27, 58.5), color=BLUE)
    sheet.arrow((73, 64), (73, 58.5), color=TEAL)
    sheet.box(5, 51, 43, 7.5, "Save selected outputs", "TIFF images · ROI ZIPs · CSV tables", color=BLUE)
    sheet.box(54, 51, 41, 7.5, "View images + objects", "napari / Fiji (live streaming)", color=TEAL)
    sheet.text(50, 47.8, "Saving and live viewing can be enabled independently.",
               ha="center", size=10, color=MUTED)

    sheet.panel("B", "One neuron has the same identity in each saved output", 3, 43.5)
    selected_coordinates = np.concatenate([coords for _, info, coords in shapes
                                            if info[subject_id_key] == SELECTED_NEURON])
    margin = 25
    left, top = np.maximum(0, np.floor(selected_coordinates.min(axis=0)).astype(int) - margin)
    right, bottom = np.minimum(image.shape[::-1], np.ceil(selected_coordinates.max(axis=0)).astype(int) + margin)
    axis = sheet.figure.add_axes((.05, .155, .40, .255))
    axis.imshow(image, cmap="gray", vmin=0, vmax=255, interpolation="nearest")
    for _, info, coordinates in shapes:
        selected = info[subject_id_key] == SELECTED_NEURON
        axis.plot(coordinates[:, 0], coordinates[:, 1], color=ORANGE if selected else "#8ba7ba",
                  linewidth=1.3 if selected else .45, alpha=1 if selected else .55)
    axis.set(xlim=(left, right), ylim=(bottom, top))
    axis.set_axis_off()
    axis.set_title(f"Saved review image · neuron {SELECTED_NEURON}", fontsize=10, color=PURPLE)
    sheet.text(72, 40.2, "Saved per-neuron measurements", size=10, ha="center", color=ORANGE)
    table_axis = sheet.figure.add_axes((.50, .185, .44, .19))
    table_axis.set_axis_off()
    columns = (table_binding.id_field, "processes", "branches")
    table = table_axis.table(
        cellText=[[row[column] for column in columns] for row in rows],
        colLabels=["Neuron ID", "Processes", "Branches"],
        cellLoc="center", colLoc="center", bbox=(0, 0, 1, 1),
    )
    table.auto_set_font_size(False)
    table.set_fontsize(10)
    for (r, c), cell in table.get_celld().items():
        cell.set_edgecolor("#d8e2ea")
        cell.set_linewidth(.5)
        if r == 0:
            cell.set_facecolor(PALE)
            cell.set_text_props(weight="bold", color=BLUE)
        elif int(rows[r - 1][table_binding.id_field]) == SELECTED_NEURON:
            cell.set_facecolor("#fff0d9")
            cell.set_text_props(weight="bold", color=ORANGE)
    sheet.text(72, 16, "Same source image + neuron ID", size=10, color=PURPLE, ha="center")
    sheet.text(5, 12.5, "Public NeuronCyto II field · retained corrected run · selected detail replotted", size=9.5, color=MUTED)

    sheet.panel("C", "Inspect linked results in napari", 3, 8.8)
    for x, title, color in ((5, "Feature-table row", BLUE), (37, "Object outline", PURPLE),
                             (69, "Its graph paths", TEAL)):
        sheet.box(x, 1.4, 26, 4.8, title, color=color)
    sheet.arrow((31, 3.8), (37, 3.8), color=PURPLE, both=True)
    sheet.arrow((63, 3.8), (69, 3.8), color=PURPLE, both=True)
    sheet.save()

    path = OUTPUT / "outputs_and_inspection_provenance.json"
    receipt = json.loads(path.read_text())
    receipt["generator_sha256"] = digest(Path(__file__))
    receipt["source_sha256"]["paper/figures/build_slas_visual_story.py"] = digest(
        Path(__file__).with_name("build_slas_visual_story.py")
    )
    receipt["retained_execution"] = {
        "kind": "post_qa_corrected_recapture", "openhcs_version": corrected["openhcs_version"],
        "published_record_execution_sha256": corrected["execution_record_sha256"],
        "summary_counts_match": True,
    }
    receipt["identity_validation"] = {
        "shared_object_subject_token": token,
        "measurement_id_field_from_declaration": table_binding.id_field,
        "roi_id_field_from_declaration": roi_binding.id_field,
        "graph_id_field_from_declaration": graph_binding.id_field,
        "measurement_and_roi_ids": sorted(row_ids), "selected_neuron": SELECTED_NEURON,
        "selected_roi_members": [name for name, info, _ in shapes if info[subject_id_key] == SELECTED_NEURON],
        "selected_graph_members": [name for name, info, _ in graph_shapes if info[subject_id_key] == SELECTED_NEURON],
    }
    receipt["saved_measurement_rows"] = list(rows)
    receipt["table_display_columns"] = list(columns)
    receipt["image_display"] = {
        "source_shape": list(image.shape), "vmin": 0, "vmax": 255,
        "crop_xyxy": [int(left), int(top), int(right), int(bottom)],
        "contours": "Unmodified saved ImageJ ROI coordinates; neuron 2 highlighted editorially",
    }
    receipt["declared_output_formats"] = {
        spec.name: [option.primary_output_suffix for option in spec.materialization.outputs]
        for spec in (UNIFIED_NEURONS_OUTPUT, NEURITE_CELLS_OUTPUT, NEURITE_MORPHOLOGY_OUTPUT)
    }
    receipt["interpretation"] = (
        "Panels A/C explain current output and native-viewer behavior from implementation. "
        "Panel B is an editorial replot of existing public NeuronCytoII corrected-recapture "
        "TIFF/ROI/CSV outputs, not a UI screenshot or a new analysis. The measurement CSV in "
        "B is distinct from napari's native per-shape feature table in C. Its rows share the "
        "object source and ID through the function's declared output relations. No physical "
        "length or area values are displayed; image intensities and stored contours are unchanged."
    )
    path.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    build()
