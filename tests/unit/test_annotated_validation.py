"""Scientific checks for independent annotation scoring, never agent pipelines."""

import hashlib
import json

import numpy as np
import pytest
import tifffile
import imageio.v3 as iio

from benchmark.annotated_validation import (
    BoundaryMetrics,
    boundary_score_007,
    CellFieldScore,
    CorpusReceipt,
    closed_outline_interiors,
    control_score_013,
    decode_039,
    FileChecksum,
    freeze_prediction_directory,
    FrozenPredictionSet,
    DatasetId,
    EvaluationField,
    InputChannel,
    InputEncoding,
    instance_score,
    InstanceMetrics,
    NuclearFieldScore,
    read_labels,
    PlateWell,
    PlateRole,
    Partition,
    score_007_partition,
    score_translocation_well_013,
    ScientificTask,
    summarize_nuclear_partition,
    summarize_cell_partition,
    Treatment,
)
from openhcs.serialization.json import to_jsonable


def test_official039_decoder_separates_reused_colors_and_touching_intensities(tmp_path):
    image = np.zeros((5, 7, 3), dtype=np.uint8)
    image[1:3, 1:3] = [10, 20, 30]
    image[1:3, 3:5] = [11, 20, 30]
    image[4, 6] = [10, 20, 30]
    path = tmp_path / "truth.png"
    iio.imwrite(path, image)
    truth = decode_039(path)
    assert truth.max() == 3
    assert truth[1, 1] != truth[1, 3]
    assert truth[1, 1] != truth[4, 6]


def test_object_matching_is_invariant_to_sparse_ids_and_reports_merge():
    truth = np.array([[0, 7, 7, 0, 99, 99]])
    exact = np.array([[0, 90000, 90000, 0, 12, 12]])
    score = instance_score(exact, truth)
    assert score.matched == 2
    assert score.object_f1 == 1
    merged = np.array([[0, 3, 3, 0, 3, 3]])
    score = instance_score(merged, truth)
    assert score.matched == 1
    assert score.merged_predicted_instances_overlap_ge_10pct == 1
    assert score.count_error == -1


def test_missing_objects_do_not_become_perfect_scores():
    truth = np.array([[0, 1], [0, 1]])
    score = instance_score(np.zeros_like(truth), truth)
    assert score.object_f1 == 0
    assert score.pixel_dice == 0
    assert score.false_negative == 1


def test_prediction_reader_rejects_overlay_or_noninteger_payload(tmp_path):
    rgb = tmp_path / "overlay.tif"
    tifffile.imwrite(rgb, np.ones((10, 10, 3), dtype=np.uint8), photometric="rgb")
    with pytest.raises(ValueError, match="scalar"):
        read_labels(rgb)
    floating = tmp_path / "floating.tif"
    tifffile.imwrite(floating, np.ones((10, 10), dtype=np.float32))
    with pytest.raises(ValueError, match="integer"):
        read_labels(floating)


def test_open007_outline_is_not_silently_closed():
    outline = np.zeros((10, 10), dtype=bool)
    outline[2, 2:8] = outline[7, 2:8] = True
    outline[2:8, 2] = outline[2:8, 7] = True
    assert closed_outline_interiors(outline)[0].max() == 1
    outline[2, 4] = False
    assert closed_outline_interiors(outline)[0].max() == 0


def test_007_boundary_metric_excludes_exterior_and_scores_exact_internal_boundary():
    cells = np.zeros((12, 12), dtype=int)
    cells[2:10, 2:6], cells[2:10, 6:10] = 1, 2
    outline = np.zeros_like(cells, dtype=bool)
    outline[2:10, 5:7] = True
    score = boundary_score_007(cells, outline)
    assert score.relevant_boundary_pixels == 12
    assert score.adjacent_boundary_within_2px_fraction == 1
    assert (
        boundary_score_007(
            (cells > 0).astype(int), outline
        ).adjacent_boundary_within_2px_fraction
        is None
    )


def test_013_controls_are_separate_treatments_and_well_replicates():
    plate = [
        {"well": "A01", "treatment": "Wortmannin", "role": "negative"},
        {"well": "B01", "treatment": "Wortmannin", "role": "negative"},
        {"well": "A12", "treatment": "Wortmannin", "role": "positive"},
        {"well": "B12", "treatment": "Wortmannin", "role": "positive"},
        {"well": "E01", "treatment": "LY294002", "role": "positive"},
    ]
    records = tuple(
        PlateWell(p["well"], Treatment(p["treatment"]), 0.0, "nM", PlateRole(p["role"]))
        for p in plate
    )
    score = control_score_013(
        {"A01": 1.0, "B01": 1.0, "A12": 5.0, "B12": 5.0, "E01": 8.0}, records
    )
    wort, ly = score.treatments
    assert wort.z_prime == 1
    assert wort.positive_n == 2
    assert ly.positive_n == 1
    assert ly.z_prime is None


def test_013_endpoint_requires_and_averages_matched_object_domains(tmp_path):
    output = tmp_path / "outputs" / "A04_w1_measurements.csv"
    output.parent.mkdir()
    output.write_text(
        "object_label,Intensity_MeanIntensity_GFP,object_name,source_image_name\n"
        "1,6.0,FilteredNuclei,GFP\n"
        "2,10.0,FilteredNuclei,GFP\n"
        "1,3.0,Cytoplasm,GFP\n"
        "2,2.0,Cytoplasm,GFP\n"
    )
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    manifest = tmp_path / "outputs.sha256"
    manifest.write_text(f"{digest}  outputs/{output.name}\n")
    frozen = FrozenPredictionSet.from_sha256sum(tmp_path, manifest)

    score = score_translocation_well_013(
        frozen,
        "A04",
        nuclear_object_name="FilteredNuclei",
        cytoplasmic_object_name="Cytoplasm",
        source_image_name="GFP",
    )

    assert score.cells == 2
    assert score.mean_nuclear_cytoplasmic_gfp_ratio == 3.5


def test_013_endpoint_rejects_mismatched_object_domains(tmp_path):
    output = tmp_path / "outputs" / "A04_w1_measurements.csv"
    output.parent.mkdir()
    output.write_text(
        "object_label,Intensity_MeanIntensity_GFP,object_name,source_image_name\n"
        "1,6.0,FilteredNuclei,GFP\n"
        "2,3.0,Cytoplasm,GFP\n"
    )
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    manifest = tmp_path / "outputs.sha256"
    manifest.write_text(f"{digest}  outputs/{output.name}\n")
    frozen = FrozenPredictionSet.from_sha256sum(tmp_path, manifest)

    with pytest.raises(ValueError, match="matched nuclear/cytoplasmic object domain"):
        score_translocation_well_013(
            frozen,
            "A04",
            nuclear_object_name="FilteredNuclei",
            cytoplasmic_object_name="Cytoplasm",
            source_image_name="GFP",
        )


def test_frozen_prediction_set_binds_encoded_source_to_verified_label(tmp_path):
    output = tmp_path / "native_outputs" / "A01%5Fs001%5Fw1.tif_step.labels.tif"
    output.parent.mkdir()
    tifffile.imwrite(output, np.ones((2, 2), dtype=np.uint16))
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    manifest = tmp_path / "outputs.sha256"
    manifest.write_text(f"{digest}  native_outputs/{output.name}\n")

    frozen = FrozenPredictionSet.from_sha256sum(tmp_path, manifest)

    assert frozen.unique_source_artifact("A01_s001_w1.tif", ".labels.tif") == output


def test_frozen_prediction_set_binds_prepared_components_to_materialized_label(
    tmp_path,
):
    output = tmp_path / "native_outputs" / "A01_w2_step.labels.tif"
    output.parent.mkdir()
    tifffile.imwrite(output, np.ones((2, 2), dtype=np.uint16))
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    manifest = tmp_path / "outputs.sha256"
    manifest.write_text(f"{digest}  native_outputs/{output.name}\n")

    frozen = FrozenPredictionSet.from_sha256sum(tmp_path, manifest)

    assert frozen.unique_component_artifact("A01", 2, ".labels.tif") == output


def test_frozen_prediction_set_refuses_changed_prediction(tmp_path):
    output = tmp_path / "prediction.labels.tif"
    output.write_bytes(b"changed")
    manifest = tmp_path / "outputs.sha256"
    manifest.write_text(f"{'0' * 64}  {output.name}\n")

    with pytest.raises(ValueError, match="checksum mismatch"):
        FrozenPredictionSet.from_sha256sum(tmp_path, manifest)


def test_prediction_freeze_is_relative_verifiable_and_immutable(tmp_path):
    predictions = tmp_path / "predictions"
    predictions.mkdir()
    (predictions / "one.bin").write_bytes(b"one")
    manifest = tmp_path / "predictions.sha256"

    receipt = freeze_prediction_directory(tmp_path, predictions, manifest)
    frozen = FrozenPredictionSet.from_sha256sum(tmp_path, manifest)

    assert receipt.artifact_count == 1
    assert frozen.artifacts[0].filename == "predictions/one.bin"
    with pytest.raises(FileExistsError):
        freeze_prediction_directory(tmp_path, predictions, manifest)


def test_nuclear_partition_summary_uses_pooled_instance_counts():
    first = InstanceMetrics(0.5, 2, 2, 2, 0, 0, 1.0, 1.0, 1.0, 0.8, 0, 0, 0)
    second = InstanceMetrics(0.5, 2, 1, 1, 0, 1, 1.0, 0.5, 2 / 3, 0.6, 1, 0, -1)
    fields = tuple(
        NuclearFieldScore(
            FileChecksum(f"prediction-{index}", "a" * 64),
            FileChecksum(f"truth-{index}", "b" * 64),
            metrics,
        )
        for index, metrics in enumerate((first, second))
    )

    summary = summarize_nuclear_partition(fields)

    assert summary.true_instances == 4
    assert summary.predicted_instances == 3
    assert summary.matched == 3
    assert summary.object_f1 == pytest.approx(6 / 7)
    assert summary.count_error == -1


def test_cell_partition_summary_distinguishes_pooled_and_field_boundary_scores():
    fields = (
        CellFieldScore(
            FileChecksum("nuclei-1", "a" * 64),
            FileChecksum("cells-1", "b" * 64),
            4,
            1,
            1,
            5,
            5,
            0,
            0,
            BoundaryMetrics(100, 80, 0.8),
        ),
        CellFieldScore(
            FileChecksum("nuclei-2", "c" * 64),
            FileChecksum("cells-2", "d" * 64),
            2,
            2,
            -1,
            1,
            1,
            1,
            0,
            BoundaryMetrics(10, 2, 0.2),
        ),
    )

    summary = summarize_cell_partition(fields)

    assert summary.manual_nucleus_closed_interiors == 6
    assert summary.predicted_nucleus_count == 6
    assert summary.nuclear_count_error_vs_closed_interiors == 0
    assert summary.predicted_cell_count == 6
    assert summary.nuclei_without_cell_overlap == 1
    assert summary.pooled_adjacent_boundary_within_2px_fraction == pytest.approx(
        82 / 110
    )
    assert summary.mean_field_adjacent_boundary_within_2px_fraction == pytest.approx(
        0.5
    )


def test_cell_partition_score_binds_each_declared_channel_to_frozen_labels(tmp_path):
    corpus_root = tmp_path / "corpus"
    trial_root = tmp_path / "trial"
    corpus_root.mkdir()
    trial_root.mkdir()
    shape = (12, 12)
    channels = tuple(
        InputChannel(
            identity,
            f"inputs/BBBC007/development/A01_s001_w{index}_z001_t001.tif",
            f"source-{index}.tif",
            str(index) * 64,
            str(index + 2) * 64,
            str(index + 4) * 64,
            shape,
            "uint8",
            InputEncoding.SCALAR,
            0,
        )
        for index, identity in ((1, "DNA"), (2, "Actin"))
    )
    annotation_root = corpus_root / "evaluation" / "BBBC007" / "A01"
    annotation_root.mkdir(parents=True)
    nuclei_outline = np.zeros(shape, dtype=np.uint8)
    nuclei_outline[3, 3:7] = nuclei_outline[7, 3:7] = 1
    nuclei_outline[3:8, 3] = nuclei_outline[3:8, 7] = 1
    cell_outline = np.zeros(shape, dtype=np.uint8)
    cell_outline[2:10, 5:7] = 1
    tifffile.imwrite(annotation_root / "nuclei_outlines.tif", nuclei_outline)
    tifffile.imwrite(annotation_root / "cell_outlines.tif", cell_outline)
    field = EvaluationField(
        DatasetId.CELLS_007,
        ScientificTask.SEEDED_CELLS,
        Partition.DEVELOPMENT,
        "A01",
        channels,
        (
            "evaluation/BBBC007/A01/nuclei_outlines.tif",
            "evaluation/BBBC007/A01/cell_outlines.tif",
        ),
        "field-1",
    )
    corpus = CorpusReceipt(1, "test", True, (), (field,), ())
    (corpus_root / "manifest.json").write_text(
        json.dumps(to_jsonable(corpus), indent=2) + "\n"
    )

    output_root = trial_root / "outputs"
    output_root.mkdir()
    nuclei = np.zeros(shape, dtype=np.uint16)
    nuclei[4:7, 4:7] = 1
    cells = np.zeros(shape, dtype=np.uint16)
    cells[2:10, 2:6] = 1
    cells[2:10, 6:10] = 2
    tifffile.imwrite(
        output_root / "A01_w1_step.labels.tif",
        nuclei,
    )
    tifffile.imwrite(
        output_root / "A01_w2_step.labels.tif",
        cells,
    )
    prediction_manifest = trial_root / "outputs.sha256"
    freeze_prediction_directory(trial_root, output_root, prediction_manifest)

    score = score_007_partition(
        corpus_root,
        trial_root,
        prediction_manifest,
        Partition.DEVELOPMENT,
    )

    assert score.metrics.fields == 1
    assert score.metrics.manual_nucleus_closed_interiors == 1
    assert score.metrics.predicted_nucleus_count == 1
    assert score.metrics.predicted_cell_count == 2
