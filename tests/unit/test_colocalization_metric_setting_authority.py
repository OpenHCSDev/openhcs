"""Metric rows, rather than a native UI visibility row, select measurements."""

from pathlib import Path

import pytest

from openhcs.core.function_patterns import normalize_function_pattern
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.interop.cellprofiler.pipeline_import import import_cellprofiler_pipeline
from openhcs.interop.cellprofiler.setting_names import setting_names
from openhcs.interop.cellprofiler.settings_binder import SettingsBinder
from openhcs.processing.backends.cellprofiler.colocalization import (
    MeasureColocalizationModule,
)


@pytest.mark.parametrize("run_all", ("Yes", "No", "Accurate"))
@pytest.mark.parametrize(
    "disabled", MeasureColocalizationModule.metric_flag_setting_bindings
)
def test_ui_visibility_setting_cannot_enable_a_disabled_metric(run_all, disabled):
    module_type = MeasureColocalizationModule
    module = ModuleBlock(
        name=module_type.module_name,
        module_num=14,
        setting_records=[
            ModuleSetting("Select images to measure", "DNA, RNA"),
            ModuleSetting("Select where to measure correlation", "Both"),
            ModuleSetting("Select objects to measure", "Nuclei"),
            ModuleSetting(module_type.run_all_metrics_setting, run_all),
            *(
                ModuleSetting(
                    setting_names(binding.setting_name)[0],
                    "No" if binding is disabled else "Yes",
                )
                for binding in module_type.metric_flag_setting_bindings
            ),
            ModuleSetting("Method for Costes thresholding", "Faster"),
        ],
    )
    bound = module_type.bind_settings(module, binder=SettingsBinder())
    for binding in module_type.metric_flag_setting_bindings:
        assert bound.kwargs[binding.require_parameter_name()] is (
            binding is not disabled
        )
    assert bound.unmapped_kwargs == {}
    assert all(record.status.is_covered for record in bound.setting_coverage)


def _colocalization_kwargs(steps):
    selected = [step for step in steps if step.name == "MeasureColocalization"]
    assert len(selected) == 1
    return tuple(
        item.kwargs_dict
        for item in normalize_function_pattern(selected[0].func).iter_items()
    )


def test_authored_beginner_costes_flag_survives_public_lowering_and_roundtrip():
    cppipe = (
        Path(__file__).parents[2]
        / "benchmark"
        / "native_refs"
        / "official30_scoped_rows"
        / "CellProfiler_tutorials_cp_tutorial_beginner_segmentation_final_wells_include_first1"
        / "native_cellprofiler_headless"
        / "segmentation_final.cppipe"
    )
    steps, _config = import_cellprofiler_pipeline(cppipe)
    original = _colocalization_kwargs(steps)
    assert len(original) == 4
    assert all(item["do_costes"] is False for item in original)
    source = FunctionStepTransportAuthority.source_from_pipeline(steps)
    namespace = {}
    exec(compile(source, "beginner_metric_settings.py", "exec"), namespace)
    restored = FunctionStepTransportAuthority.pipeline_steps_from_namespace(namespace)
    assert _colocalization_kwargs(restored) == original


@pytest.mark.parametrize(
    "disabled,families",
    (
        ("do_correlation", {"correlation", "slope"}),
        ("do_manders", {"manders"}),
        ("do_rwc", {"RWC"}),
        ("do_overlap", {"overlap", "k"}),
        ("do_costes", {"costes"}),
    ),
)
def test_recorded_source_pair_features_exclude_disabled_metrics(disabled, families):
    from dataclasses import fields

    import numpy as np

    from openhcs.core.measurement_row_materialization import (
        ConcatenatedColumnarRows,
        DataclassMeasurementColumnarRows,
    )
    from openhcs.interop.cellprofiler.runtime.invocation import (
        CellProfilerMeasurementImage,
    )
    from openhcs.interop.cellprofiler.runtime.object_measurement_row_policies import (
        SourcePairObjectMeasurementInvocation,
    )
    from openhcs.processing.backends.cellprofiler.colocalization import (
        ColocalizationMeasurements,
        MeasureColocalizationObjectMeasurementRowPolicy,
        ObjectColocalizationMetricArrays,
    )

    image = CellProfilerMeasurementImage(
        source_image_name="DNA__RNA",
        source_aliases=("DNA", "RNA"),
        payload=np.zeros((2, 2, 2), dtype=np.float32),
    )
    source_pair = image.source_image_pairs()[0]
    object_rows = ObjectColocalizationMetricArrays.empty(2).rows_for(
        np.asarray((1, 2), dtype=np.int32)
    )
    image_row = ColocalizationMeasurements(
        **{
            field.name: (0 if field.name == "slice_index" else 0.25)
            for field in fields(ColocalizationMeasurements)
        }
    )
    image_rows = DataclassMeasurementColumnarRows(
        (image_row,), row_type=ColocalizationMeasurements
    )
    invocation = SourcePairObjectMeasurementInvocation(
        kwargs={disabled: False},
        source_pair=source_pair,
    )
    projected = MeasureColocalizationObjectMeasurementRowPolicy().project_rows(
        ConcatenatedColumnarRows((image_rows, object_rows)),
        invocation,
    )
    for raw_rows, selected_rows in zip(
        (image_rows, object_rows), projected.row_batches
    ):
        enabled = MeasureColocalizationModule.project_source_pair_columnar_rows(
            raw_rows, source_pair
        )
        expected_names = tuple(
            name
            for name in enabled.columns
            if not any(
                name.startswith(
                    f"Correlation_{(family if family == "RWC" else family.title())}_"
                )
                for family in families
            )
        )
        assert tuple(selected_rows.columns) == expected_names
        for name in expected_names:
            np.testing.assert_array_equal(
                selected_rows.column_values(name), enabled.column_values(name)
            )
        assert selected_rows.row_count() == raw_rows.row_count()


def test_disabled_costes_does_not_run_threshold_search_and_preserves_other_values(
    monkeypatch,
):
    from dataclasses import replace

    import numpy as np

    from openhcs.processing.backends.cellprofiler import colocalization as module

    first = np.linspace(0.01, 0.95, 64, dtype=np.float32)
    second = np.roll(first, 5).copy()
    options = module.ColocalizationMeasurementOptions(
        threshold_percent=15.0,
        do_correlation=True,
        do_manders=True,
        do_rwc=True,
        do_overlap=True,
        do_costes=True,
        costes_method=module.CostesMethod.FASTER,
        scale_max=255,
    )
    enabled = module._colocalization_measurement(first, second, options=options)

    def unexpected_threshold_search(*args, **kwargs):
        raise AssertionError("disabled Costes reached its numerical threshold search")

    monkeypatch.setattr(
        module.NumbaNumpyColocalizationCostesBackendStrategy,
        "scaled_second_channel_costes",
        unexpected_threshold_search,
    )
    disabled = module._colocalization_measurement(
        first,
        second,
        options=replace(options, do_costes=False),
    )
    for feature in module.MeasureColocalizationModule.MeasurementFeature:
        if feature.source_pair_relation.metric_parameter_name != "do_costes":
            field_name = feature.measurement_row_field_name
            assert getattr(disabled, field_name) == getattr(enabled, field_name)
    np.testing.assert_array_equal(first, np.linspace(0.01, 0.95, 64, dtype=np.float32))
    np.testing.assert_array_equal(second, np.roll(first, 5))
