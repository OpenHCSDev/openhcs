"""Benchmark-only terminal reference export derivation tests."""

from __future__ import annotations

import re
from pathlib import Path

import imageio.v3 as imageio
import numpy as np
import pytest

from benchmark.cellprofiler_reference_exports import (
    CellProfilerReferenceArtifactComparison,
    CellProfilerReferenceExportArtifact,
    CellProfilerReferenceExportPlan,
    ReferenceExportSemanticKind,
)
from openhcs.interop.cellprofiler import import_cellprofiler_pipeline
from openhcs.interop.cellprofiler.parser import CPPipeParser

REFERENCE_ROOT = Path("benchmark/native_refs/official30_scoped_rows")
EMPTY_PROFILE_PIPELINES = {
    "cp4_supplement_combine_objects": REFERENCE_ROOT
    / "CellProfiler4_benchmark_supplement_cp4_supplement_combine_objects_wells_include_first1"
    / "native_cellprofiler_headless"
    / "CombineObjectsDemo.cppipe",
    "cp_tutorial_translocation_start": REFERENCE_ROOT
    / "CellProfiler_tutorials_cp_tutorial_translocation_start_wells_include_first1"
    / "native_cellprofiler_headless"
    / "Translocation_start.cppipe",
    "ExampleIlluminationCorrection_Example1_EachMethod": REFERENCE_ROOT
    / "ExampleIlluminationCorrection_ExampleIlluminationCorrection_Example1_EachMethod_wells_include_first1"
    / "native_cellprofiler_headless"
    / "ExampleIlluminationCorrection_Example1_EachMethod.cppipe",
    "ExampleIlluminationCorrection_Example2": REFERENCE_ROOT
    / "ExampleIlluminationCorrection_ExampleIlluminationCorrection_Example2_wells_include_first1"
    / "native_cellprofiler_headless"
    / "ExampleIlluminationCorrection_Example2.cppipe",
    "ExampleIlluminationCorrection_Example3": REFERENCE_ROOT
    / "ExampleIlluminationCorrection_ExampleIlluminationCorrection_Example3_wells_include_first1"
    / "native_cellprofiler_headless"
    / "ExampleIlluminationCorrection_Example3.cppipe",
}
EXPECTED_TERMINAL_EXPORTS = {
    "cp4_supplement_combine_objects": ("CombinedObjects",),
    "cp_tutorial_translocation_start": ("Nuclei",),
    "ExampleIlluminationCorrection_Example1_EachMethod": ("CorrGreen",),
    "ExampleIlluminationCorrection_Example2": (
        "UncorrectedNuclei",
        "SmallBlockCorrectedNuclei",
        "LargeBlockCorrectedNuclei",
    ),
    "ExampleIlluminationCorrection_Example3": (
        "PolynomialCorrected",
        "ConvexHullCorrWorm",
    ),
}


def test_reference_export_comparison_uses_declared_semantics(tmp_path: Path) -> None:
    categorical = CellProfilerReferenceExportArtifact(
        artifact_name="Labels",
        artifact_type="ObjectLabelsArtifactType",
        semantic_kind=ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS,
        output_filename="labels.tiff",
        comparison="integer label pixels: exact equality",
    )
    numeric = CellProfilerReferenceExportArtifact(
        artifact_name="Image",
        artifact_type="ImageArtifactType",
        semantic_kind=ReferenceExportSemanticKind.NUMERIC_IMAGE_PIXELS,
        output_filename="image.npy",
        comparison="float pixels: atol=1e-6, rtol=1e-6, zero mismatches",
    )
    reference_labels = np.asarray([[0, 2_000_000]], dtype=np.uint32)
    candidate_labels = np.asarray([[0, 2_000_001]], dtype=np.uint32)
    imageio.imwrite(tmp_path / "reference_labels.tiff", reference_labels)
    imageio.imwrite(tmp_path / "candidate_labels.tiff", candidate_labels)
    reference_image = np.asarray([[0.5, 1.0]], dtype=np.float32)
    candidate_image = reference_image + np.asarray([[1e-7, 1e-7]], dtype=np.float32)
    np.save(tmp_path / "reference_image.npy", reference_image)
    np.save(tmp_path / "candidate_image.npy", candidate_image)

    categorical_comparison = CellProfilerReferenceArtifactComparison.compare(
        categorical,
        tmp_path / "reference_labels.tiff",
        tmp_path / "candidate_labels.tiff",
    )
    numeric_comparison = CellProfilerReferenceArtifactComparison.compare(
        numeric,
        tmp_path / "reference_image.npy",
        tmp_path / "candidate_image.npy",
    )

    assert categorical_comparison.equivalent is False
    assert categorical_comparison.different_pixel_count == 1
    assert categorical_comparison.out_of_tolerance_pixel_count is None
    assert numeric_comparison.equivalent is True
    assert numeric_comparison.out_of_tolerance_pixel_count == 0


def test_categorical_comparison_projects_only_explicit_single_plane_stack(
    tmp_path: Path,
) -> None:
    artifact = CellProfilerReferenceExportArtifact(
        artifact_name="Labels",
        artifact_type="ObjectLabelsArtifactType",
        semantic_kind=ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS,
        output_filename="labels.tiff",
        comparison="integer label pixels: exact equality",
    )
    labels = np.asarray([[0, 1], [2, 0]], dtype=np.uint16)
    imageio.imwrite(tmp_path / "reference.tiff", labels)
    imageio.imwrite(tmp_path / "candidate.tiff", labels[np.newaxis, ...])

    comparison = CellProfilerReferenceArtifactComparison.compare(
        artifact,
        tmp_path / "reference.tiff",
        tmp_path / "candidate.tiff",
    )

    assert comparison.equivalent is True
    assert comparison.compared_pixel_count == labels.size
    assert comparison.reference_shape == labels.shape
    assert comparison.candidate_shape == (1, *labels.shape)


def test_categorical_comparison_rejects_non_plane_dimension_mismatch(
    tmp_path: Path,
) -> None:
    artifact = CellProfilerReferenceExportArtifact(
        artifact_name="Labels",
        artifact_type="ObjectLabelsArtifactType",
        semantic_kind=ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS,
        output_filename="labels.tiff",
        comparison="integer label pixels: exact equality",
    )
    labels = np.asarray([[0, 1], [2, 0]], dtype=np.uint16)
    imageio.imwrite(tmp_path / "reference.tiff", labels)
    imageio.imwrite(tmp_path / "candidate.tiff", labels[..., np.newaxis])

    comparison = CellProfilerReferenceArtifactComparison.compare(
        artifact,
        tmp_path / "reference.tiff",
        tmp_path / "candidate.tiff",
    )

    assert comparison.equivalent is False
    assert comparison.compared_pixel_count == 0


def test_reference_export_plan_compares_exact_declared_inventory(
    tmp_path: Path,
) -> None:
    artifact = CellProfilerReferenceExportArtifact(
        artifact_name="Labels",
        artifact_type="ObjectLabelsArtifactType",
        semantic_kind=ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS,
        output_filename="labels.tiff",
        comparison="integer label pixels: exact equality",
    )
    plan = CellProfilerReferenceExportPlan(
        source_pipeline_name="source.cppipe",
        source_sha256="source",
        artifacts=(artifact,),
    )
    reference_root = tmp_path / "reference"
    candidate_root = tmp_path / "candidate"
    reference_root.mkdir()
    candidate_root.mkdir()
    labels = np.asarray([[0, 1], [2, 0]], dtype=np.uint16)
    imageio.imwrite(reference_root / artifact.output_filename, labels)
    imageio.imwrite(candidate_root / artifact.output_filename, labels[np.newaxis, ...])

    (comparison,) = plan.compare_output_roots(reference_root, candidate_root)

    assert comparison.equivalent is True

    imageio.imwrite(candidate_root / "extra.tiff", labels)
    with pytest.raises(ValueError, match="candidate output inventory differs"):
        plan.compare_output_roots(reference_root, candidate_root)

    (candidate_root / "extra.tiff").unlink()
    (candidate_root / artifact.output_filename).unlink()
    with pytest.raises(ValueError, match="candidate output inventory differs"):
        plan.compare_output_roots(reference_root, candidate_root)


def test_reference_export_plan_selects_declared_runtime_observation_paths(
    tmp_path: Path,
) -> None:
    artifact = CellProfilerReferenceExportArtifact(
        artifact_name="Labels",
        artifact_type="ObjectLabelsArtifactType",
        semantic_kind=ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS,
        output_filename="labels.tiff",
        comparison="integer label pixels: exact equality",
    )
    plan = CellProfilerReferenceExportPlan(
        source_pipeline_name="source.cppipe",
        source_sha256="source",
        artifacts=(artifact,),
    )
    reference_root = tmp_path / "reference"
    runtime_root = tmp_path / "runtime"
    reference_root.mkdir()
    runtime_root.mkdir()
    labels = np.asarray([[0, 1], [2, 0]], dtype=np.uint16)
    reference_path = reference_root / artifact.output_filename
    candidate_path = runtime_root / artifact.output_filename
    unrelated_path = runtime_root / "intermediate.tiff"
    imageio.imwrite(reference_path, labels)
    imageio.imwrite(candidate_path, labels[np.newaxis, ...])
    imageio.imwrite(unrelated_path, labels)

    (comparison,) = plan.compare_observed_outputs(
        reference_root,
        (unrelated_path, candidate_path),
    )

    assert comparison.equivalent is True


@pytest.mark.parametrize("case_name", tuple(EMPTY_PROFILE_PIPELINES))
def test_reference_export_plan_derives_terminal_artifacts_from_declarations(
    case_name: str,
) -> None:
    pipeline_path = EMPTY_PROFILE_PIPELINES[case_name]

    plan = CellProfilerReferenceExportPlan.from_pipeline(
        pipeline_path,
        source_root=pipeline_path.parent,
    )

    assert (
        tuple(artifact.artifact_name for artifact in plan.artifacts)
        == (EXPECTED_TERMINAL_EXPORTS[case_name])
    )
    for artifact in plan.artifacts:
        if (
            artifact.semantic_kind
            is ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS
        ):
            assert artifact.output_filename.endswith(".tiff")
            assert artifact.comparison == "integer label pixels: exact equality"
        else:
            assert artifact.output_filename.endswith(".npy")
            assert artifact.comparison.startswith("float pixels:")


@pytest.mark.parametrize("case_name", tuple(EMPTY_PROFILE_PIPELINES))
def test_reference_export_pipeline_only_changes_header_and_appends_exporters(
    case_name: str,
    tmp_path: Path,
) -> None:
    pipeline_path = EMPTY_PROFILE_PIPELINES[case_name]
    source_text = pipeline_path.read_text(encoding="utf-8")
    plan = CellProfilerReferenceExportPlan.from_pipeline(
        pipeline_path,
        source_root=pipeline_path.parent,
    )
    output_path = tmp_path / pipeline_path.name

    plan.materialize(pipeline_path, output_path)

    loaded_plan = CellProfilerReferenceExportPlan.from_sidecar(
        output_path.with_suffix(".reference_exports.json")
    )
    loaded_plan.validate_generated_pipeline(output_path)

    rendered = output_path.read_text(encoding="utf-8")
    original_count = int(
        re.search(r"^ModuleCount:(\d+)$", source_text, re.MULTILINE)[1]
    )
    added_count = len(plan.artifacts) + sum(
        artifact.semantic_kind is ReferenceExportSemanticKind.CATEGORICAL_OBJECT_LABELS
        for artifact in plan.artifacts
    )
    expected_prefix = re.sub(
        r"^ModuleCount:\d+$",
        f"ModuleCount:{original_count + added_count}",
        source_text,
        count=1,
        flags=re.MULTILINE,
    ).rstrip()
    assert rendered.startswith(expected_prefix + "\n\n")

    modules = CPPipeParser(output_path).parse()
    assert len(modules) == original_count + added_count
    steps, _pipeline_config = import_cellprofiler_pipeline(
        output_path,
        source_root=pipeline_path.parent,
    )
    assert steps
