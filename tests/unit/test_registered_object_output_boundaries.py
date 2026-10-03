"""Synthetic controls at the original shape-row and FilterObjects owners."""

import numpy as np
import pytest

from openhcs.core.artifacts import (
    ArtifactSpec,
    ArtifactSpecCollection,
    ObjectLabelsArtifactType,
)
from openhcs.core.function_patterns import FunctionInvocationKey
from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
from openhcs.core.pipeline.artifact_planning import artifact_producers_for_outputs
from openhcs.core.runtime_artifact_queries import MeasurementLabelSliceFeatureQuery
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
    ObjectFeatureArrayDomain,
    ObjectFeatureValueTable,
)
from openhcs.core.runtime_object_label_domains import ObjectLabelDomain
from openhcs.core.runtime_object_labels import (
    ObjectLabelPayload,
    ObjectLabelVariantData,
)
from openhcs.core.runtime_output_matching import RuntimeReturnedOutputMatcher
from openhcs.core.runtime_plane_projection import RuntimePlaneProjection
from openhcs.core.runtime_tabular_values import MeasurementObjectRowIdentity
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_LOOKUP_DIALECT,
)
from openhcs.interop.cellprofiler.parser import ModuleBlock, ModuleSetting
from openhcs.processing.backends.cellprofiler.object_filtering import (
    FilterMode,
    FilterObjectsModule,
    filter_objects,
)
from openhcs.processing.backends.cellprofiler.shape import (
    MeasureObjectSizeShapeModule,
    measure_object_size_shape,
)


def _payload(labels, ids):
    return ObjectLabelPayload(
        variant_data=ObjectLabelVariantData(labels=labels),
        domain=ObjectLabelDomain(declared_object_ids=ids),
    )


@pytest.mark.parametrize("dimensions", (2, 3))
@pytest.mark.parametrize("declared_ids", ((2, 7), (1, 2, 7)))
def test_categorical_shape_rows_survive_completion_and_original_feature_lookup(
    dimensions, declared_ids
):
    plane = np.zeros((12, 15), dtype=np.int32)
    plane[2:4, 2:5] = 2
    plane[6:10, 8:13] = 7
    labels = plane if dimensions == 2 else np.stack((plane, plane))
    payload = _payload(labels, declared_ids)
    _image, rows = measure_object_size_shape(
        np.zeros(labels.shape, dtype=np.float32),
        payload,
        calculate_advanced=False,
        calculate_zernikes=False,
    )
    assert tuple(rows.column_values("object_label")) == declared_ids
    assert rows.object_row_identity is MeasurementObjectRowIdentity.LABEL_ID
    completed = MeasureObjectSizeShapeModule.runtime_object_measurement_row_policy().complete_rows(
        rows,
        label_payload=payload,
    )
    assert completed is rows
    projected = MeasureObjectSizeShapeModule.project_measurement_record_rows(
        rows, source_image_name=None
    )
    table = MeasurementTable(
        name="Shape",
        rows=projected,
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Objects"),
        measurement_feature_owner=MeasureObjectSizeShapeModule,
    )
    feature = "AreaShape_Area" if dimensions == 2 else "AreaShape_Volume"
    (values,) = MeasurementLabelSliceFeatureQuery(
        measurement_tables=(table,),
        feature_name=feature,
        object_name="Objects",
        dialect=CELLPROFILER_MEASUREMENT_LOOKUP_DIALECT,
        plane_projector=RuntimePlaneProjection.stack(1),
    ).values_for_labels(payload)
    multiplier = 1 if dimensions == 2 else 2
    expected = [6 * multiplier, 20 * multiplier]
    if declared_ids[0] == 1:
        expected.insert(0, np.nan)
    np.testing.assert_allclose(values, expected, rtol=0, atol=0, equal_nan=True)


class _AnnotateObjects:
    def complete_row(self, row):
        row["annotation"] = row[self.object_id_field] * 10
        super().complete_row(row)


class _StampSlice:
    def complete_row(self, row):
        row["stamp"] = self.slice_index
        super().complete_row(row)


class _IndependentFeatureTable(_AnnotateObjects, _StampSlice, ObjectFeatureValueTable):
    feature_array_domains = {"OrdinalFeature": ObjectFeatureArrayDomain.ROW_ORDINAL}


def test_independent_declared_feature_and_cooperative_capabilities_need_no_consumer_edits():
    table = _IndependentFeatureTable.from_feature_arrays(
        {
            "CompactFeature": np.asarray((44.0, 66.0)),
            "OrdinalFeature": np.asarray((11.0, 22.0, 33.0)),
        },
        measured_object_ids=(2, 7),
        object_domain=(1, 2, 7),
        slice_index=4,
    )
    rows = table.rows()
    assert [row["annotation"] for row in rows] == [10, 20, 70]
    assert [row["stamp"] for row in rows] == [4, 4, 4]
    assert [row["OrdinalFeature"] for row in rows] == [11.0, 22.0, 33.0]
    assert np.isnan(rows[0]["CompactFeature"])
    assert [row["CompactFeature"] for row in rows[1:]] == [44.0, 66.0]


def _filter_contract(removed):
    source = ArtifactSpec.output("Objects", ObjectLabelsArtifactType)
    module = ModuleBlock(
        name="FilterObjects",
        module_num=3,
        enabled=True,
        setting_records=[
            ModuleSetting(name, value)
            for name, value in (
                ("Select the object to filter", "Objects"),
                ("Name the output objects", "Retained"),
                ("Filter using classifier rules or measurements?", "Border"),
                ("Select the filtering method", "Limits"),
                ("Additional object count", "0"),
                ("Keep removed objects as a separate set?", "Yes" if removed else "No"),
                ("Name the objects removed by the filter", "Removed"),
            )
        ],
    )
    return FilterObjectsModule.callable_contract(
        module=module,
        invocation_key=FunctionInvocationKey("filter_objects", "default", 0),
        step_context=ArtifactDeclarationStepContext(
            step_name="Filter",
            step_index=3,
            available_artifacts=ArtifactSpecCollection((source,)),
            available_artifact_producers=artifact_producers_for_outputs(
                (source,),
                groups=(None,),
                invocation_keys=(
                    FunctionInvocationKey("fixture_producer", "default", 0),
                ),
            ),
            main_flow_artifacts=ArtifactSpecCollection(()),
        ),
    )


@pytest.mark.parametrize("removed", (False, True))
@pytest.mark.parametrize("empty", (False, True))
def test_optional_removed_declaration_validates_and_matches_exact_runtime_slots(
    removed, empty
):
    assert FilterObjectsModule.require_callable() is filter_objects
    contract = _filter_contract(removed)
    FilterObjectsModule.validate_callable_artifact_abi(filter_objects, contract)
    image = np.zeros((12, 15), dtype=np.float32)
    labels = np.zeros(image.shape, dtype=np.int32)
    if not empty:
        labels[:2, 2:5] = 2
        labels[6:10, 8:13] = 7
    result = filter_objects(
        image,
        mode=FilterMode.BORDER,
        object_labels=(_payload(labels, () if empty else (2, 7)),),
        emit_removed_objects=removed,
    )
    assert len(result) == (6 if removed else 4)
    resolved = RuntimeReturnedOutputMatcher(contract, result).resolve()
    assert len(resolved) == len(contract.artifact_outputs)
    assert result[-1].source_ids == (() if empty else ((2,) if removed else (7,)))
    assert result[-1].target_ids == (() if empty else (1,))
    with pytest.raises(ValueError, match="trailing return count"):
        RuntimeReturnedOutputMatcher(contract, result[:-1]).resolve()


def test_optional_return_annotation_does_not_weaken_object_identity_validation():
    contract = _filter_contract(True)

    def invalid_array_return(
        image,
    ) -> tuple[np.ndarray, object, np.ndarray, np.ndarray, object, object]:
        raise AssertionError("not executed")

    with pytest.raises(TypeError, match="ObjectLabelValue"):
        FilterObjectsModule.validate_callable_artifact_abi(
            invalid_array_return, contract
        )
