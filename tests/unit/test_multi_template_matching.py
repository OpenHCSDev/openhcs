from __future__ import annotations

import inspect
from pathlib import Path
from types import SimpleNamespace

import cv2
import numpy as np
import pytest

from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ImageArtifactType,
    SpecialArtifactType,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.pipeline.materialization_flag_planner import (
    MaterializationFlagPlanner,
)
from openhcs.core.runtime_output_matching import RuntimeReturnedOutputMatcher
from openhcs.processing.backends.analysis import multi_template_matching
from openhcs.processing.backends.analysis.multi_template_matching import (
    OpenCVTemplateMatchMethod,
    TemplateMatchResult,
    multi_template_crop,
    multi_template_crop_reference_channel,
    multi_template_crop_subset,
)
from openhcs.processing.materialization import materialization_outputs
from openhcs.processing.materialization.options import MaterializedFilenameIdentity


@pytest.mark.parametrize(
    "function",
    (
        multi_template_crop,
        multi_template_crop_reference_channel,
        multi_template_crop_subset,
    ),
)
def test_public_template_matching_routes_selected_method_to_mtm(
    monkeypatch: pytest.MonkeyPatch,
    function,
) -> None:
    received_methods: list[int] = []

    monkeypatch.setattr(
        multi_template_matching.cv2,
        "imread",
        lambda *_args, **_kwargs: np.ones((2, 2), dtype=np.uint8),
    )

    def match_templates(*_args, **kwargs):
        received_methods.append(kwargs["method"])
        return []

    monkeypatch.setattr(
        multi_template_matching.MTM,
        "matchTemplates",
        match_templates,
    )

    inspect.unwrap(function)(
        np.ones((1, 4, 4), dtype=np.uint8),
        Path("template.tif"),
        method=OpenCVTemplateMatchMethod.SQDIFF,
        crop_enabled=False,
    )

    assert received_methods == [int(OpenCVTemplateMatchMethod.SQDIFF)]


def test_template_match_artifact_materializes_every_match_column() -> None:
    [artifact_spec] = (
        spec
        for spec in CallableContract.from_callable(
            multi_template_crop_reference_channel
        ).artifact_outputs
        if spec.artifact_type is SpecialArtifactType
    )
    assert not artifact_spec.materialization.uses_source_identity_filename()
    assert (
        artifact_spec.materialization.outputs[0].filename_identity
        is MaterializedFilenameIdentity.ARTIFACT_NAME
    )
    results = [
        TemplateMatchResult(
            slice_index=2,
            matches=[
                ("first", (1, 2, 3, 4), 0.95),
                ("second", (5, 6, 7, 8), 0.85),
            ],
            best_match=("first", (1, 2, 3, 4), 0.95),
            crop_bbox=(1, 2, 3, 4),
            match_score=0.95,
            num_matches=2,
            best_rotation_angle=0.0,
        )
    ]

    [output] = materialization_outputs(
        artifact_spec.materialization,
        results,
        "/analysis/match_results.pkl",
        SimpleNamespace(),
    )

    assert output.path == "/analysis/match_results_mtm_matches.csv"
    lines = output.content.splitlines()
    assert lines[0].split(",") == [
        "slice_index",
        "match_id",
        "bbox_x",
        "bbox_y",
        "bbox_width",
        "bbox_height",
        "confidence_score",
        "template_name",
        "is_best_match",
        "was_cropped",
    ]
    assert len(lines) == 3
    assert "slice_2_match_0" in lines[1]
    assert "slice_2_match_1" in lines[2]


@pytest.mark.parametrize(
    "function",
    [
        multi_template_crop,
        multi_template_crop_reference_channel,
        multi_template_crop_subset,
    ],
)
def test_template_crop_declares_changed_image_flow_and_materialization(
    function, tmp_path
):
    image = np.random.default_rng(17).integers(0, 256, (1, 20, 30), dtype=np.uint8)
    template = image[0, 5:11, 7:15].copy()
    template_path = tmp_path / "template.tif"
    assert cv2.imwrite(str(template_path), template)
    result = function(image, template_path, normalize_input=False, rotate_result=False)
    np.testing.assert_array_equal(result[0], template[None, ...])

    contract = CallableContract.from_callable(function)
    assert not contract.preserves_input_main_flow()
    [image_spec] = contract.main_flow_outputs
    assert image_spec.artifact_type is ImageArtifactType
    assert not image_spec.materialization.uses_source_identity_filename()
    matched = RuntimeReturnedOutputMatcher(contract, result).resolve()
    np.testing.assert_array_equal(matched[image_spec.ref()], template[None, ...])
    plans = {
        spec.ref(): ArtifactOutputPlan(
            spec.name,
            str(tmp_path / spec.name),
            spec.artifact_type,
            materialization=spec.materialization,
        )
        for spec in contract.artifact_outputs
    }
    step_plan = CompiledStepPlan(
        0, "crop", "FunctionStep", "R02C05", artifact_outputs=plans
    )
    assert MaterializationFlagPlanner._step_materializes_images(step_plan)
