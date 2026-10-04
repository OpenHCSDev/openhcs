from __future__ import annotations

from collections import Counter
import math

from openhcs.core.measurement_feature_queries import (
    ColumnarMeasurementTableSchema,
    MeasurementAxisValueProjection,
    MeasurementFeatureQuery,
    MeasurementFeatureValueIndex,
)
from openhcs.core.measurement_lookup_dialect import RuntimeMeasurementLookupDialect
from openhcs.core.measurement_row_materialization import MeasurementSparseColumnarRows
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    MeasurementSubject,
    MeasurementTable,
)
from openhcs.core.runtime_tabular_values import FieldSpec


def _lookup_dialect() -> RuntimeMeasurementLookupDialect:
    return RuntimeMeasurementLookupDialect(
        category_prefixes=(("intensity",), ("area", "shape")),
        alternative_feature_part_aliases={
            ("area",): (("volume",),),
        },
        source_qualified_feature_families=(("mean", "intensity"),),
    )


def test_source_family_scan_decomposes_immutable_lookup_once() -> None:
    provider_calls: Counter[str] = Counter()

    def category_prefixes() -> tuple[tuple[str, ...], ...]:
        provider_calls["category_prefixes"] += 1
        return (("intensity",),)

    def feature_part_aliases() -> dict[tuple[str, ...], tuple[str, ...]]:
        provider_calls["feature_part_aliases"] += 1
        return {}

    def source_families() -> tuple[tuple[str, ...], ...]:
        provider_calls["source_families"] += 1
        return (
            *((f"unrelated_{index}",) for index in range(64)),
            ("mean", "intensity"),
        )

    dialect = RuntimeMeasurementLookupDialect(
        category_prefixes_provider=category_prefixes,
        feature_part_aliases_provider=feature_part_aliases,
        source_qualified_feature_families_provider=source_families,
    )

    families = dialect.feature_lookup(
        "Intensity_MeanIntensity_DNA"
    ).source_qualified_feature_families

    assert families == (("mean", "intensity"),)
    assert provider_calls == {
        "category_prefixes": 1,
        "feature_part_aliases": 1,
        "source_families": 1,
    }


def test_lookup_preserves_source_qualification_aliases_and_object_domain() -> None:
    dialect = _lookup_dialect()
    source_lookup = dialect.feature_lookup("Intensity_MeanIntensity_DNA")
    alias_lookup = dialect.feature_lookup("AreaShape_Area")

    assert source_lookup.dialect_feature_parts == ("mean", "intensity", "dna")
    assert source_lookup.source_qualified_feature_families == (("mean", "intensity"),)
    assert source_lookup.source_aliases == ("dna",)
    assert source_lookup.source_qualified_field_names == (
        "mean_intensity",
        "meanintensity",
    )
    assert alias_lookup.field_aliases == (
        "area_shape_area",
        "areashapearea",
        "area",
        "volume",
    )
    assert source_lookup.query_object_name("Nuclei") == "Nuclei"


def test_columnar_lookup_distinguishes_source_object_absence_padding_and_nan() -> None:
    feature_field = "mean_intensity"
    table = MeasurementTable(
        name="Measurements",
        rows=MeasurementSparseColumnarRows.from_rows(
            (
                {
                    "object_name": "Nuclei",
                    "object_label": 1,
                    "source_image_name": "DNA",
                    feature_field: 1.5,
                },
                {
                    "object_name": "Nuclei",
                    "object_label": 2,
                    "source_image_name": "DNA",
                    feature_field: None,
                },
                {
                    "object_name": "Nuclei",
                    "object_label": 3,
                    "source_image_name": "DNA",
                },
                {
                    "object_name": "Nuclei",
                    "object_label": 4,
                    "source_image_name": "DNA",
                    feature_field: float("nan"),
                },
                {
                    "object_name": "Cells",
                    "object_label": 1,
                    "source_image_name": "DNA",
                    feature_field: 8.0,
                },
                {
                    "object_name": "Nuclei",
                    "object_label": 1,
                    "source_image_name": "RNA",
                    feature_field: 9.0,
                },
            ),
            fields=(
                FieldSpec("object_name", str),
                FieldSpec("object_label", int),
                FieldSpec("source_image_name", str),
                FieldSpec(feature_field, float, required=False),
            ),
        ),
        subject=MeasurementSubject(MeasurementScope.ARTIFACT, "Measurements"),
    )
    query = MeasurementFeatureQuery(
        "Intensity_MeanIntensity_DNA",
        object_name="Nuclei",
        dialect=_lookup_dialect(),
    )

    default_indexes = MeasurementFeatureValueIndex.from_columnar_table_by_object(
        table,
        query,
        {"Nuclei": "Nuclei"},
    )
    explicit_nan_indexes = MeasurementFeatureValueIndex.from_columnar_table_by_object(
        table,
        query,
        {"Nuclei": "Nuclei"},
        measurement_value_qualifier=(
            lambda value: isinstance(value, float) and math.isnan(value)
        ),
    )

    assert default_indexes is not None
    assert default_indexes["Nuclei"].values_by_label == {1: 1.5}
    assert explicit_nan_indexes is not None
    explicit_nan_values = explicit_nan_indexes["Nuclei"].values_by_label
    assert set(explicit_nan_values) == {4}
    assert math.isnan(explicit_nan_values[4])


def test_feature_batch_preserves_overlapping_axes_last_write_and_live_columns() -> None:
    import numpy as np
    from openhcs.core.runtime_measurements import MeasurementRowAxisField
    from openhcs.core.measurement_row_materialization import MEASUREMENT_SPARSE_CELL

    ids = np.asarray([1, 1, 2, 3, 4], dtype=object)
    first = np.asarray([5.0, 7.0, np.nan, MEASUREMENT_SPARSE_CELL, None], dtype=object)
    table = MeasurementTable(
        name="MutableCells",
        subject=MeasurementSubject(
            MeasurementScope.OBJECT, "Cells", id_field="cell_key"
        ),
        rows=MeasurementSparseColumnarRows(
            columns={
                "cell_key": ids,
                "slice_index": (None, 0, 1, 0, 1),
                "first": first,
                "second": (1.0, None, 8.0, 9.0, 10.0),
            },
            fields=(
                FieldSpec("cell_key", int),
                FieldSpec("slice_index", int),
                FieldSpec("first", float),
                FieldSpec("second", float),
            ),
        ),
    )
    schema = ColumnarMeasurementTableSchema.from_table(table)
    queries = {
        name: MeasurementFeatureQuery(name, object_name="Cells")
        for name in ("first", "second")
    }
    objects = {
        name: {"Cells": query.query_object_name} for name, query in queries.items()
    }
    masks = {
        axis: MeasurementAxisValueProjection(
            MeasurementRowAxisField.SLICE_INDEX, axis
        ).mask(table.rows.column_values("slice_index"))
        for axis in (0, 1)
    }

    def project():
        return {
            feature: {
                axis: indexes["Cells"].values_by_label for axis, indexes in axes.items()
            }
            for feature, axes in schema.feature_value_indexes(
                table,
                queries,
                objects,
                index_type=MeasurementFeatureValueIndex,
                row_masks=masks,
            )
        }

    initial = project()
    assert initial == {
        "first": {0: {1: 7.0}, 1: {1: 5.0}},
        "second": {0: {1: 1.0, 3: 9.0}, 1: {1: 1.0, 2: 8.0, 4: 10.0}},
    }
    ids[0] = 9
    first[0] = 15.0
    changed = project()
    assert changed["first"] == {0: {9: 15.0, 1: 7.0}, 1: {9: 15.0}}
    assert changed["second"][1] == {9: 1.0, 2: 8.0, 4: 10.0}
    assert initial["first"][1] == {1: 5.0}


def test_feature_batch_keeps_alias_column_priority_and_feature_qualification() -> None:
    import numpy as np
    from openhcs.core.measurement_row_materialization import MEASUREMENT_SPARSE_CELL

    table = MeasurementTable(
        name="SourceQualified",
        subject=MeasurementSubject(MeasurementScope.OBJECT, "Nuclei"),
        rows=MeasurementSparseColumnarRows(
            columns={
                "object_label": (1, 2, 3, 3, 5),
                "source_image_name": ("DNA", "DNA", "DNA", "DNA", "Memb"),
                "mean-intensity": (None, np.nan, 3.0, MEASUREMENT_SPARSE_CELL, 5.0),
                "mean intensity": (1.0, 2.0, 9.0, 4.0, 99.0),
            },
            fields=(
                FieldSpec("object_label", int),
                FieldSpec("source_image_name", str),
                FieldSpec("mean-intensity", float),
                FieldSpec("mean intensity", float),
            ),
        ),
    )
    queries = {
        source: MeasurementFeatureQuery(
            f"Intensity_MeanIntensity_{source}",
            object_name="Nuclei",
            dialect=_lookup_dialect(),
        )
        for source in ("DNA", "Memb")
    }
    objects = {
        source: {"Nuclei": query.query_object_name} for source, query in queries.items()
    }
    schema = ColumnarMeasurementTableSchema.from_table(table)
    default = {
        feature: axes[None]["Nuclei"].values_by_label
        for feature, axes in schema.feature_value_indexes(
            table, queries, objects, index_type=MeasurementFeatureValueIndex
        )
    }
    assert default == {"DNA": {1: 1.0, 2: 2.0, 3: 4.0}, "Memb": {5: 5.0}}
    qualified = {
        feature: axes[None]["Nuclei"].values_by_label
        for feature, axes in schema.non_absent_feature_value_indexes(
            table,
            queries,
            objects,
            index_type=MeasurementFeatureValueIndex,
        )
    }
    assert qualified["DNA"][1] == 1.0
    assert np.isnan(qualified["DNA"][2])
    assert qualified["DNA"][3] == 4.0
    assert qualified["Memb"] == {5: 5.0}


def test_shared_rows_keep_table_subject_and_result_constructor_authorities() -> None:
    import pytest
    from openhcs.core.measurement_feature_queries import (
        ColumnarMeasurementTableSchema,
    )

    rows = MeasurementSparseColumnarRows(
        columns={
            "object_name": ("Cells", "Nuclei"),
            "object_label": [1, 2],
            "cell_key": [1, 2],
            "nucleus_key": (10, 20),
            "area": (2.0, 3.0),
        },
        fields=(
            FieldSpec("object_name", str),
            FieldSpec("object_label", int),
            FieldSpec("cell_key", int),
            FieldSpec("nucleus_key", int),
            FieldSpec("area", float),
        ),
    )
    fixed = MeasurementTable(
        name="Fixed",
        rows=rows,
        subject=MeasurementSubject(
            MeasurementScope.OBJECT, "Cells", id_field="cell_key"
        ),
    )
    nuclei = MeasurementTable(
        name="Nuclei",
        rows=rows,
        subject=MeasurementSubject(
            MeasurementScope.OBJECT, "Nuclei", id_field="nucleus_key"
        ),
    )
    mixed = MeasurementTable(
        name="Mixed",
        rows=rows,
        subject=MeasurementSubject(
            MeasurementScope.ARTIFACT, "Mixed", id_field="cell_key"
        ),
    )
    first_schema = ColumnarMeasurementTableSchema.from_table(fixed)
    first = (first_schema.object_names(fixed), first_schema.feature_names(fixed))
    second_schema = ColumnarMeasurementTableSchema.from_table(nuclei)
    second = (second_schema.object_names(nuclei), second_schema.feature_names(nuclei))
    combined_schema = ColumnarMeasurementTableSchema.from_table(mixed)
    combined = (
        combined_schema.object_names(mixed),
        combined_schema.feature_names(mixed),
    )
    assert first[0] == ("Cells",)
    assert second[0] == ("Nuclei",)
    assert combined[0] == ("Cells", "Nuclei")
    assert "cell_key" not in first[1] and "nucleus_key" in first[1]
    assert "nucleus_key" not in second[1] and "cell_key" in second[1]

    class PositiveLabelIndex(MeasurementFeatureValueIndex):
        def __init__(self, values_by_label=None, positional_values=None):
            super().__init__(values_by_label or {}, positional_values or [])
            if any(label <= 0 for label in self.values_by_label):
                raise ValueError("Positive label index requires positive labels")

    query = MeasurementFeatureQuery("area", object_name="Nuclei")
    indexed = PositiveLabelIndex.from_columnar_table_by_object(
        mixed, query, {"Nuclei": "Nuclei"}
    )
    assert isinstance(indexed["Nuclei"], PositiveLabelIndex)
    assert indexed["Nuclei"].values_by_label == {2: 3.0}
    rows.columns["object_label"][1] = -2
    with pytest.raises(ValueError, match="requires positive labels"):
        PositiveLabelIndex.from_columnar_table_by_object(
            mixed, query, {"Nuclei": "Nuclei"}
        )
