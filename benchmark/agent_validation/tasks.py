"""Pinned human-eval-bia task declarations.

The scoring cases below are manual, typed transcriptions of the ``check``
functions at commit ``f6edaa15545e84951f5428d07e16db04155f2266``. The
notebook and check-cell hashes make drift independently detectable without
executing the upstream benchmark harness.
"""

from __future__ import annotations

from pathlib import Path

import numpy as np
import pandas as pd

from benchmark.agent_validation.contracts import (
    AssertionResult,
    DiagnosticCheck,
    DslRequirement,
    FunctionAvailabilityExpectation,
    OutputKind,
    ScoringCase,
    TaskInput,
    UpstreamTaskSource,
)
from benchmark.agent_validation.declarations import ValidationTaskDeclaration

UPSTREAM_REPOSITORY = "https://github.com/haesleinhuepf/human-eval-bia.git"
UPSTREAM_COMMIT = "f6edaa15545e84951f5428d07e16db04155f2266"
UPSTREAM_LICENCE = "MIT"

STANDARD_IMAGE_DIAGNOSTICS = (
    DiagnosticCheck.MULTI_PERCENTILE,
    DiagnosticCheck.NORMALIZATION_SCOPE,
    DiagnosticCheck.MISSED_SIGNAL,
    DiagnosticCheck.UNSUPPORTED_MASK,
    DiagnosticCheck.SATURATION,
    DiagnosticCheck.FOREGROUND_DISTRIBUTION,
)
STANDARD_PIPELINE_DSL = (
    DslRequirement.VARIABLE_COMPONENTS,
    DslRequirement.GROUP_BY,
    DslRequirement.ARTIFACT_MATERIALIZATION,
    DslRequirement.COMPILE_RUN_BOUNDARY,
)


def _source(
    notebook: str,
    notebook_sha256: str,
    check_source_sha256: str,
) -> UpstreamTaskSource:
    return UpstreamTaskSource(
        repository_url=UPSTREAM_REPOSITORY,
        commit=UPSTREAM_COMMIT,
        notebook_path=Path("test_cases") / f"{notebook}.ipynb",
        notebook_sha256=notebook_sha256,
        check_source_sha256=check_source_sha256,
        licence=UPSTREAM_LICENCE,
    )


def _array_assertion(
    expected: object, actual: object, name: str = "array_equal"
) -> tuple[AssertionResult, ...]:
    expected_array = np.asarray(expected)
    actual_array = np.asarray(actual)
    passed = np.array_equal(expected_array, actual_array)
    mismatch = (
        int(np.count_nonzero(expected_array != actual_array))
        if expected_array.shape == actual_array.shape
        else -1
    )
    return (
        AssertionResult(
            name=name,
            passed=passed,
            detail=(
                f"expected_shape={expected_array.shape}; actual_shape={actual_array.shape}; "
                f"mismatch_count={mismatch}"
            ),
        ),
    )


class OtsuPositivePixelCountTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.otsu_positive_pixel_count"
    prompt = (
        "Implement apply_otsu_threshold_and_count_postiive_pixels(image): apply "
        "Otsu thresholding and return the number of positive pixels."
    )
    output_kind = OutputKind.SCALAR
    function_availability = FunctionAvailabilityExpectation.CUSTOM_FUNCTION_REQUIRED
    source = _source(
        "apply_otsu_threshold_and_count_postiive_pixels",
        "515c26a1ded23cb73d86defe1cd4628bedf7bfa3e74858a06947faa39b9e23b9",
        "29f2a9c92f99008569d25fbba23bb763706ddfd764e2df32e0e8a7edc24a9f6b",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS + (
        DiagnosticCheck.COUNT_DISTRIBUTION,
    )
    required_dsl = STANDARD_PIPELINE_DSL + (DslRequirement.SIGNATURE_DERIVED_EXPOSURE,)
    dsl_instruction = (
        "Search the live catalogue first. If the composite scalar-producing operation "
        "is absent, register one typed function and verify its signature-derived code, "
        "UI and MCP projections before compiling."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        arrays = (
            (
                [
                    [0, 0, 0, 0, 0],
                    [1, 1, 1, 0, 0],
                    [1, 1, 1, 0, 0],
                    [1, 0, 0, 0, 0],
                    [0, 0, 0, 1, 0],
                ],
                8,
            ),
            (
                [
                    [0, 0, 0, 0, 0],
                    [0, 1, 0, 0, 0],
                    [1, 2, 1, 0, 0],
                    [0, 1, 3, 4, 0],
                    [0, 1, 4, 1, 0],
                ],
                4,
            ),
            (np.zeros((5, 5), dtype=np.uint8), 0),
        )
        return tuple(
            ScoringCase(
                f"case-{index}", (TaskInput("image", np.asarray(image)),), expected
            )
            for index, (image, expected) in enumerate(arrays, start=1)
        )

    @classmethod
    def assert_case(
        cls, case: ScoringCase, actual: object
    ) -> tuple[AssertionResult, ...]:
        value = int(np.asarray(actual).reshape(-1)[0])
        return (
            AssertionResult(
                "scalar_equal",
                value == case.expected,
                f"expected={case.expected}; actual={value}",
            ),
        )


class BinaryClosingTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.binary_closing"
    prompt = "Implement binary_closing(binary_image, radius: int = 1) with a square footprint."
    output_kind = OutputKind.ARRAY
    function_availability = FunctionAvailabilityExpectation.REGISTRY_FIRST
    source = _source(
        "binary_closing",
        "55bda0f64333ee98719e340df70d39d4be1d86c605b2cf3304c1794586fde76d",
        "1ec85bda79a70050f0f04765c61fc8382a677303371fcfdcd10e33eebd6fef9d",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS + (
        DiagnosticCheck.SPLIT,
        DiagnosticCheck.MERGE,
    )
    required_dsl = STANDARD_PIPELINE_DSL + (DslRequirement.SEQUENTIAL_FUNCTION_PATTERN,)
    dsl_instruction = (
        "Start from the catalogue's registered binary-closing operation. Prove that "
        "its reflected footprint contract can express the required square radius; if "
        "it cannot, treat that parameter boundary as the exact custom-function gap."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        image = np.asarray(
            [
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 1, 0, 1, 0, 0],
                [0, 0, 1, 0, 1, 0, 0],
                [0, 0, 1, 0, 1, 0, 0],
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0, 0, 0],
            ]
        )
        expected = np.asarray(
            [
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 1, 1, 1, 0, 0],
                [0, 0, 1, 1, 1, 0, 0],
                [0, 0, 1, 1, 1, 0, 0],
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0, 0, 0],
            ]
        )
        return (
            ScoringCase(
                "case-1",
                (TaskInput("binary_image", image),),
                expected,
                (("radius", 1),),
            ),
        )

    assert_case = classmethod(
        lambda cls, case, actual: _array_assertion(case.expected, actual)
    )


class BinarySkeletonTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.binary_skeleton"
    prompt = (
        "Implement binary_skeleton(binary_image) for a two-dimensional binary image."
    )
    output_kind = OutputKind.ARRAY
    function_availability = FunctionAvailabilityExpectation.REGISTRY_FIRST
    source = _source(
        "binary_skeleton",
        "48316317451b9140a459957be6402c38a987ee844dd017824ef2d9ce80378b00",
        "8e05de0c8d9ce40b326e4d8e346890899f53e4b8f638940ec0aff5f8ce86a658",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS + (
        DiagnosticCheck.DISCONNECTED_TRACE,
        DiagnosticCheck.CROSSING_OWNERSHIP,
    )
    required_dsl = STANDARD_PIPELINE_DSL
    dsl_instruction = (
        "Use a compatible registered skeletonization function and preserve the binary "
        "plane as one bounded site through compile, run and materialization."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        image = np.asarray(
            [
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 1, 1, 1, 0, 0],
                [0, 0, 1, 1, 1, 0, 0],
                [0, 1, 1, 1, 1, 1, 0],
                [0, 1, 1, 1, 1, 1, 0],
                [0, 1, 1, 1, 1, 1, 0],
                [0, 0, 0, 0, 0, 0, 0],
            ]
        )
        reference = np.asarray(
            [
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 1, 0, 0, 0],
                [0, 0, 0, 1, 0, 0, 0],
                [0, 0, 0, 1, 0, 0, 0],
                [0, 1, 1, 1, 1, 1, 0],
                [0, 0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0, 0, 0],
            ]
        )
        return (ScoringCase("case-1", (TaskInput("binary_image", image),), reference),)

    @classmethod
    def assert_case(
        cls, case: ScoringCase, actual: object
    ) -> tuple[AssertionResult, ...]:
        delta = int(
            np.abs(np.abs(np.asarray(actual)) - np.abs(np.asarray(case.expected))).sum()
        )
        return (
            AssertionResult(
                "absolute_pixel_error_at_most_3",
                delta <= 3,
                f"absolute_pixel_error={delta}",
            ),
        )


class DetectEdgesTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.detect_edges"
    prompt = "Implement detect_edges(image) using an edge-detection filter."
    output_kind = OutputKind.ARRAY
    function_availability = FunctionAvailabilityExpectation.REGISTRY_FIRST
    source = _source(
        "detect_edges",
        "9495a6cb2d480b1eb6659b1524a6cfe202c49f5daba6eb2cc680c0f18bab594d",
        "8d62a307071228112bf9e8e9f815d68ae19d48d3b37abbd2b4435261d2a9a146",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS + (DiagnosticCheck.TILE_SEAM,)
    required_dsl = STANDARD_PIPELINE_DSL
    dsl_instruction = (
        "Resolve Sobel/edge detection through the live catalogue and validate the "
        "materialized edge image without introducing a second callable implementation."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        image = np.asarray([[1, 1, 2, 2, 2]] * 5)
        return (ScoringCase("case-1", (TaskInput("image", image),), None),)

    @classmethod
    def assert_case(
        cls, case: ScoringCase, actual: object
    ) -> tuple[AssertionResult, ...]:
        result = np.asarray(actual)
        edge_zero = (
            result[:, 0].max() == 0
            and result[:, 0].min() == 0
            and result[:, -1].max() == 0
        )
        centre_nonzero = result[:, 1:4].max() != 0 or result[:, 1:4].min() != 0
        return (
            AssertionResult(
                "outer_columns_zero",
                bool(edge_zero),
                f"left={result[:, 0].tolist()}; right={result[:, -1].tolist()}",
            ),
            AssertionResult(
                "centre_contains_edge",
                bool(centre_nonzero),
                f"centre_nonzero={centre_nonzero}",
            ),
        )


class ExpandLabelsTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.expand_labels_without_overlap"
    prompt = "Implement expand_labels_without_overlap(label_image, radius: int = 1)."
    output_kind = OutputKind.LABEL_IMAGE
    function_availability = FunctionAvailabilityExpectation.CUSTOM_FUNCTION_REQUIRED
    source = _source(
        "expand_labels_without_overlap",
        "fc57867d621d4fb1fdc16484ae932baba51ff255d1f12918c2fcd7ca98e72f8b",
        "be882674f3d00c677e5152c5b85e9447a27ba696b54ed71b145e3815ee9f5c82",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS + (
        DiagnosticCheck.SPLIT,
        DiagnosticCheck.MERGE,
        DiagnosticCheck.AREA_DISTRIBUTION,
    )
    required_dsl = STANDARD_PIPELINE_DSL + (DslRequirement.SIGNATURE_DERIVED_EXPOSURE,)
    dsl_instruction = (
        "Register a typed label-expansion function when the exact operation is absent, "
        "then verify radius exposure and label-artifact materialization."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        image = np.asarray(
            [
                [0, 0, 0, 0, 0],
                [0, 1, 1, 3, 0],
                [0, 1, 1, 3, 0],
                [0, 0, 0, 0, 0],
                [2, 0, 0, 0, 0],
            ]
        )
        expected = np.asarray(
            [
                [0, 1, 1, 3, 0],
                [1, 1, 1, 3, 3],
                [1, 1, 1, 3, 3],
                [2, 1, 1, 3, 0],
                [2, 2, 0, 0, 0],
            ]
        )
        return (
            ScoringCase(
                "case-1", (TaskInput("label_image", image),), expected, (("radius", 1),)
            ),
        )

    assert_case = classmethod(
        lambda cls, case, actual: _array_assertion(case.expected, actual)
    )


class MaximumIntensityProjectionTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.maximum_intensity_projection"
    prompt = "Implement maximum_intensity_projection(image) along the first axis."
    output_kind = OutputKind.ARRAY
    function_availability = FunctionAvailabilityExpectation.REGISTRY_FIRST
    source = _source(
        "maximum_intensity_projection",
        "4f676a82317338a6769e81c344049599c60c62996496089eb13033f913bcab34",
        "ccc4665dd70ce38c8a73a88acdbd2c74860feddea200246a16e0288078ab0929",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS
    required_dsl = STANDARD_PIPELINE_DSL + (DslRequirement.SEQUENTIAL_FUNCTION_PATTERN,)
    dsl_instruction = (
        "Assemble the planes with variable_components=[Z_INDEX], keep grouping distinct, "
        "and apply the registered projection as an ordered function pattern."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        image = np.asarray(
            [
                [0, 0, 0, 0, 0, 0],
                [0, 1, 0, 0, 2, 0],
                [0, 0, 0, 0, 0, 0],
                [0, 0, 0, 0, 0, 0],
                [0, 4, 0, 0, 3, 0],
                [0, 0, 0, 0, 0, 0],
            ]
        )
        return (
            ScoringCase(
                "case-1",
                (TaskInput("image", image, stack_axis=0),),
                np.asarray([0, 4, 0, 0, 3, 0]),
            ),
        )

    assert_case = classmethod(
        lambda cls, case, actual: _array_assertion(case.expected, actual)
    )


class MeasureRegionPropertiesTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.measure_properties_of_regions"
    prompt = (
        "Implement measure_properties_of_regions(label_image, intensity_image) and "
        "return a table containing area, perimeter and mean_intensity."
    )
    output_kind = OutputKind.TABLE
    function_availability = FunctionAvailabilityExpectation.CUSTOM_FUNCTION_REQUIRED
    source = _source(
        "measure_properties_of_regions",
        "c891e2998dc25c0c6b65413a6f16d57adde242e005e6a135d5d5c7f907793a62",
        "f4f190b17fcc24bceeb055254ac255fdff6deb26c91a1459413ebf6a30002ee6",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS + (
        DiagnosticCheck.COUNT_DISTRIBUTION,
        DiagnosticCheck.AREA_DISTRIBUTION,
    )
    required_dsl = STANDARD_PIPELINE_DSL + (
        DslRequirement.SOURCE_BINDINGS,
        DslRequirement.SIGNATURE_DERIVED_EXPOSURE,
    )
    dsl_instruction = (
        "Use declared source bindings to route the label and intensity channels into a "
        "typed table-producing custom function; do not recover sources by filename in the callable."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        labels = np.asarray(
            [
                [0, 1, 0, 0, 0],
                [0, 0, 0, 0, 0],
                [0, 2, 2, 2, 2],
                [0, 3, 3, 0, 0],
                [0, 0, 0, 4, 0],
            ]
        )
        intensity = np.asarray(
            [
                [0, 2, 0, 0, 0],
                [0, 0, 0, 0, 0],
                [0, 3, 3, 4, 4],
                [0, 3, 3, 0, 0],
                [0, 0, 0, 5, 0],
            ]
        )
        return (
            ScoringCase(
                "case-1",
                (
                    TaskInput("label_image", labels, channel=1),
                    TaskInput("intensity_image", intensity, channel=2),
                ),
                ("area", "perimeter", "mean_intensity"),
            ),
        )

    @classmethod
    def assert_case(
        cls, case: ScoringCase, actual: object
    ) -> tuple[AssertionResult, ...]:
        if not isinstance(actual, pd.DataFrame):
            return (
                AssertionResult(
                    "pandas_dataframe", False, f"actual_type={type(actual).__name__}"
                ),
            )
        expected_columns = set(case.expected)
        actual_columns = set(actual.columns)
        return (
            AssertionResult(
                "required_columns",
                expected_columns.issubset(actual_columns),
                f"columns={tuple(actual.columns)}",
            ),
            AssertionResult(
                "exactly_three_columns",
                len(actual.columns) == 3,
                f"column_count={len(actual.columns)}",
            ),
            AssertionResult("four_rows", len(actual) == 4, f"row_count={len(actual)}"),
        )


class SegmentationCountingWorkflowTask(ValidationTaskDeclaration):
    task_id = "human_eval_bia.workflow_segmentation_counting"
    prompt = (
        "Segment objects whose intensity is above the image mean and return the "
        "connected-object count."
    )
    output_kind = OutputKind.SCALAR
    function_availability = FunctionAvailabilityExpectation.CUSTOM_FUNCTION_REQUIRED
    source = _source(
        "workflow_segmentation_counting",
        "46652295924b985989d3393005ec29da8befb74109bc828446734e1c3ba46c0b",
        "088826a26e5dcb218acf129ad83129c53ebe6ab782cdc3c16e02d615ad861db0",
    )
    required_diagnostics = STANDARD_IMAGE_DIAGNOSTICS + (
        DiagnosticCheck.SPLIT,
        DiagnosticCheck.MERGE,
        DiagnosticCheck.COUNT_DISTRIBUTION,
    )
    required_dsl = STANDARD_PIPELINE_DSL + (
        DslRequirement.SEQUENTIAL_FUNCTION_PATTERN,
        DslRequirement.SIGNATURE_DERIVED_EXPOSURE,
    )
    dsl_instruction = (
        "Represent thresholding, connected-component labelling and scalar counting as a "
        "reviewed sequential pattern or one typed composite when intermediate contracts "
        "cannot be expressed; document the catalogue decision."
    )

    @classmethod
    def scoring_cases(cls) -> tuple[ScoringCase, ...]:
        first = np.asarray(
            [
                [0, 0, 0, 0, 0],
                [0, 1, 0, 0, 0],
                [0, 0, 0, 2, 0],
                [0, 1, 0, 0, 0],
                [0, 0, 0, 0, 0],
            ]
        )
        second = np.asarray(
            [
                [0, 0, 0, 0, 0],
                [0, 100, 0, 90, 0],
                [0, 0, 0, 0, 0],
                [0, 110, 0, 80, 0],
                [0, 0, 0, 0, 0],
            ]
        )
        return (
            ScoringCase("case-1", (TaskInput("image", first),), 3),
            ScoringCase("case-2", (TaskInput("image", second),), 4),
        )

    @classmethod
    def assert_case(
        cls, case: ScoringCase, actual: object
    ) -> tuple[AssertionResult, ...]:
        value = int(np.asarray(actual).reshape(-1)[0])
        return (
            AssertionResult(
                "scalar_equal",
                value == case.expected,
                f"expected={case.expected}; actual={value}",
            ),
        )
