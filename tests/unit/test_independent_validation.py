from __future__ import annotations

import runpy
from pathlib import Path

import imageio.v3 as iio
import numpy as np
import pytest

from benchmark.contracts.validation import (
    ValidationAssayRole,
    ValidationEvidenceKind,
    ValidationFunctionSurface,
    ValidationImageRecord,
    ValidationPartition,
)
from benchmark.datasets.registry import get_dataset_spec
from benchmark.validation.corpus import (
    ValidationCorpusPreparer,
    derive_validation_dsl_contract,
    freeze_pipeline,
    source_bindings_for_validation,
    split_validation_records,
    verify_frozen_pipeline,
)
from benchmark.validation.references import (
    decode_bbbc007_outline,
    decode_bbbc039_mask,
)
from benchmark.validation.scoring import (
    AssayMeasurementRecord,
    _resolved_result_artifact,
    assay_quality_metrics,
    boundary_segmentation_metrics,
    instance_segmentation_metrics,
)

DATASET_IDS = (
    "BBBC039_nuclei_segmentation",
    "BBBC007_cell_boundaries",
    "BBBC013_u2os_translocation_bmp",
)


def test_independent_validation_declarations_own_exact_sources_and_tracks():
    declarations = {
        dataset_id: get_dataset_spec(dataset_id).independent_validation
        for dataset_id in DATASET_IDS
    }
    assert all(declarations.values())
    assert [
        (artifact.name, artifact.size_bytes, artifact.sha256)
        for artifact in declarations["BBBC039_nuclei_segmentation"].artifacts
    ] == [
        (
            "images.zip",
            77_915_748,
            "6f30a5d4fe38c928ded972704f085975f8dc0d65d9aa366df00e5a9d449fddd7",
        ),
        (
            "masks.zip",
            2_753_811,
            "f9e6043d8ca56344a4886f96a700d804d6ee982f31e2b2cd3194af2a053c2710",
        ),
        (
            "metadata.zip",
            17_816,
            "a2c1f900bed9ba92a99553efd4c2ae98598433691c7401d818653ab61110deb2",
        ),
    ]
    assert declarations["BBBC039_nuclei_segmentation"].source_identity_fields == (
        "plate",
        "well",
        "site",
    )
    assert declarations["BBBC007_cell_boundaries"].evidence_kind is (
        ValidationEvidenceKind.MANUAL_OUTLINES
    )
    assert declarations["BBBC013_u2os_translocation_bmp"].evidence_kind is (
        ValidationEvidenceKind.PLATE_BIOLOGY
    )
    surfaces = {
        track.function_surface
        for validation in declarations.values()
        for track in validation.authoring_tracks
    }
    assert surfaces == {
        ValidationFunctionSurface.CATALOG,
        ValidationFunctionSurface.REGISTERED_CUSTOM,
    }


def test_source_bindings_and_dsl_contract_derive_from_dataset_declaration():
    validation = get_dataset_spec("BBBC039_nuclei_segmentation").independent_validation
    records = (
        ValidationImageRecord(
            source_relative_path=Path("first.tif"),
            canonical_relative_path=Path(
                "images/plate-1_well-A01_site-1_channel-DNA.tif"
            ),
            source_set_id="1_A01_1",
            selection_key="first.tif",
            partition=ValidationPartition.TRAINING,
            well="A01",
            site="1",
            channel="DNA",
            metadata=(("plate", "1"),),
        ),
        ValidationImageRecord(
            source_relative_path=Path("second.tif"),
            canonical_relative_path=Path(
                "images/plate-1_well-A01_site-2_channel-DNA.tif"
            ),
            source_set_id="1_A01_2",
            selection_key="second.tif",
            partition=ValidationPartition.TRAINING,
            well="A01",
            site="2",
            channel="DNA",
            metadata=(("plate", "1"),),
        ),
    )

    bindings = source_bindings_for_validation(validation)
    contract = derive_validation_dsl_contract(validation, records)

    assert tuple(binding.alias for binding in bindings.bindings) == ("dna",)
    assert bindings.grouping_metadata_fields == ("plate", "well")
    assert tuple(
        join.image_metadata_field for join in bindings.imported_metadata_tables[0].joins
    ) == ("plate", "well", "site")
    assert contract.source_components == ("plate", "well", "site", "channel")
    assert contract.grouping_fields == ("plate", "well")
    assert contract.variable_components == ("site",)
    assert contract.source_set_count == 2


def test_generated_pipeline_template_is_self_contained(tmp_path):
    validation = get_dataset_spec("BBBC039_nuclei_segmentation").independent_validation
    assert validation is not None
    template = tmp_path / "pipeline_template.py"

    ValidationCorpusPreparer._write_pipeline_template(
        template,
        source_bindings_for_validation(validation),
    )

    source = template.read_text(encoding="utf-8")
    namespace = runpy.run_path(str(template))
    assert "from source_bindings import" not in source
    assert namespace["pipeline_steps"] == []
    assert tuple(
        join.image_metadata_field
        for join in namespace["pipeline_config"]
        .source_bindings_config.imported_metadata_tables[0]
        .joins
    ) == ("plate", "well", "site")


def test_paired_source_bindings_do_not_join_consumed_channel_component():
    validation = get_dataset_spec("BBBC007_cell_boundaries").independent_validation
    assert validation is not None

    bindings = source_bindings_for_validation(validation)

    assert tuple(
        join.image_metadata_field for join in bindings.imported_metadata_tables[0].joins
    ) == validation.source_identity_fields == ("well", "site")
    assert tuple(
        binding.selector.metadata[0].value for binding in bindings.bindings
    ) == ("DNA", "ACTIN")


def test_trial_splits_are_declaration_owned_disjoint_and_counted():
    for dataset_id, expected in (
        ("BBBC039_nuclei_segmentation", (4, 50)),
        ("BBBC007_cell_boundaries", (4, 12)),
        ("BBBC013_u2os_translocation_bmp", (4, 92)),
    ):
        validation = get_dataset_spec(dataset_id).independent_validation
        assert validation is not None
        assert (
            validation.trial_split.expected_development_source_sets,
            validation.trial_split.expected_held_out_source_sets,
        ) == expected


def test_trial_split_hides_held_out_sets_before_freeze():
    validation = get_dataset_spec(
        "BBBC013_u2os_translocation_bmp"
    ).independent_validation
    assert validation is not None
    records = tuple(
        ValidationImageRecord(
            source_relative_path=Path(f"{well}_{channel}.bmp"),
            canonical_relative_path=Path("images") / f"{well}_{channel}.bmp",
            source_set_id=f"{well}_1",
            selection_key=well,
            partition=ValidationPartition.COMPLETE,
            well=well,
            site="1",
            channel=channel,
        )
        for well in (
            "A04",
            "B08",
            "E04",
            "F08",
            *(f"X{index:03d}" for index in range(92)),
        )
        for channel in ("GFP", "DNA")
    )

    development, held_out = split_validation_records(validation, records)

    assert {record.selection_key for record in development} == {
        "A04",
        "B08",
        "E04",
        "F08",
    }
    assert not (
        {record.source_set_id for record in development}
        & {record.source_set_id for record in held_out}
    )


def test_pipeline_freeze_fails_closed_after_bytes_change(tmp_path):
    dataset_id = "BBBC039_nuclei_segmentation"
    (tmp_path / dataset_id).mkdir(parents=True)
    pipeline = tmp_path / "pipeline.py"
    pipeline.write_text("pipeline = 1\n", encoding="utf-8")

    receipt = freeze_pipeline(dataset_id, pipeline, corpus_root=tmp_path)

    assert verify_frozen_pipeline(dataset_id, corpus_root=tmp_path) == receipt
    pipeline.write_text("pipeline = 2\n", encoding="utf-8")
    with pytest.raises(RuntimeError, match="bytes changed"):
        verify_frozen_pipeline(dataset_id, corpus_root=tmp_path)


def test_prediction_artifacts_cannot_escape_result_directory(tmp_path):
    manifest = tmp_path / "results" / "predictions.csv"
    manifest.parent.mkdir()

    assert _resolved_result_artifact(manifest, Path("labels/A01.npy")) == (
        manifest.parent / "labels/A01.npy"
    )
    with pytest.raises(ValueError, match="escapes"):
        _resolved_result_artifact(manifest, Path("../trusted_scoring/reference.npy"))


def test_bbbc039_decoder_and_perfect_object_metrics(tmp_path):
    mask = np.zeros((8, 8, 4), dtype=np.uint8)
    mask[1:4, 1:4, 0] = 1
    mask[1:4, 4:7, 0] = 2
    mask[..., 3] = 255
    path = tmp_path / "mask.png"
    iio.imwrite(path, mask)

    reference = decode_bbbc039_mask(path)
    metrics = instance_segmentation_metrics(
        reference,
        reference,
        source_set_id="plate_A01_1",
        channel="DNA",
    )

    assert metrics.reference_count == metrics.predicted_count == 2
    assert metrics.f1 == pytest.approx(1.0)
    assert metrics.mean_matched_iou == pytest.approx(1.0)
    assert metrics.aggregated_jaccard_index == pytest.approx(1.0)
    assert metrics.panoptic_quality == pytest.approx(1.0)
    assert metrics.split_reference_count == 0
    assert metrics.merged_prediction_count == 0


def test_instance_metrics_detect_split_and_merge():
    reference = np.zeros((12, 16), dtype=np.uint16)
    reference[2:10, 1:7] = 1
    reference[2:10, 9:15] = 2
    split = reference.copy()
    split[2:10, 4:7] = 3
    merged = np.zeros_like(reference)
    merged[2:10, 1:15] = 1

    split_metrics = instance_segmentation_metrics(
        split,
        reference,
        source_set_id="split",
        channel="DNA",
    )
    merge_metrics = instance_segmentation_metrics(
        merged,
        reference,
        source_set_id="merge",
        channel="DNA",
    )

    assert split_metrics.split_reference_count == 1
    assert merge_metrics.merged_prediction_count == 1


def test_bbbc007_outline_decoder_and_published_two_pixel_boundary_metric(tmp_path):
    outline = np.ones((20, 20), dtype=np.uint8)
    outline[3:17, 3] = 0
    outline[3:17, 16] = 0
    outline[3, 3:17] = 0
    outline[16, 3:17] = 0
    outline[3:17, 10] = 0
    path = tmp_path / "outline.tif"
    iio.imwrite(path, outline)

    reference = decode_bbbc007_outline(path)
    predicted = np.zeros_like(reference)
    predicted[4:16, 4:10] = 1
    predicted[4:16, 10:16] = 2
    metrics = boundary_segmentation_metrics(
        predicted,
        reference,
        source_set_id="A01_1",
        channel="ACTIN",
    )

    assert int(reference.max()) == 2
    assert metrics.relevant_predicted_boundary_pixels > 0
    assert metrics.relevant_boundary_within_two_pixels == pytest.approx(1.0)
    assert metrics.boundary_f1_within_two_pixels > 0.9


def test_assay_statistics_use_declared_control_roles_and_replicated_doses():
    rows = tuple(
        AssayMeasurementRecord(
            well=f"A{index:02d}",
            assay_block="Wortmannin",
            treatment=("vehicle" if role == "negative_control" else "Wortmannin"),
            concentration=concentration,
            assay_role=ValidationAssayRole(role),
            value=value,
        )
        for index, (role, concentration, value) in enumerate(
            (
                ("negative_control", 0.0, 0.0),
                ("negative_control", 0.0, 0.1),
                ("positive_control", 150.0, 1.0),
                ("positive_control", 150.0, 1.1),
                ("dose", 10.0, 0.4),
                ("dose", 10.0, 0.5),
                ("dose", 20.0, 0.7),
                ("dose", 20.0, 0.8),
            ),
            start=1,
        )
    )

    metrics = assay_quality_metrics(rows, treatment="Wortmannin")

    assert metrics.negative_control_count == 2
    assert metrics.positive_control_count == 2
    assert np.asarray(metrics.dose_response_means) == pytest.approx(
        np.asarray(((10.0, 0.45), (20.0, 0.75)))
    )
    assert np.isfinite(metrics.z_prime)
    assert np.isfinite(metrics.replicate_sd_v_factor)
