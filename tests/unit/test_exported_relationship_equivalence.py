"""Saved directed edges must retain the native object-row correlations."""

from pathlib import Path

import pytest

from benchmark.equivalence.outputs import RuntimeOutputSnapshot
from benchmark.equivalence.runtime import (
    RuntimeMeasurementSnapshot,
    runtime_measurement_equivalence,
)

_HEADER = (
    "relationship_type,source_role,target_role,source_object,target_object,"
    "producer_module_number,parent_id,child_id,image_number,slice_count\n"
)


def _saved_outputs(
    root: Path, *, edges: bool, swapped: bool = False
) -> RuntimeOutputSnapshot:
    root.mkdir()
    (root / "Cells.csv").write_text(
        "ImageNumber,ObjectNumber,Children_Nuclei_Count\n"
        "1,1,1\n1,2,1\n1,3,0\n2,1,1\n2,2,1\n2,3,0\n"
    )
    parents = (2, 1) if swapped else (1, 2)
    (root / "Nuclei.csv").write_text(
        "ImageNumber,ObjectNumber,Parent_Cells\n"
        + "".join(
            f"{image},{child},{parents[child - 1]}\n"
            for image in (1, 2)
            for child in (1, 2)
        )
    )
    if edges:
        (root / "Relationships.csv").write_text(
            _HEADER
            + "".join(
                f"{kind},{source_role},{target_role},{source},{target},11,"
                f"{parents[child - 1]},{child},{image},2\n"
                for kind, source_role, target_role, source, target in (
                    ("Parent", "parent", "child", "Cells", "Nuclei"),
                    ("Child", "child", "parent", "Nuclei", "Cells"),
                )
                for image in (1, 2)
                for child in (1, 2)
            )
        )
    return RuntimeOutputSnapshot.from_output_root(root)


def test_saved_relationship_edges_join_native_parent_and_zero_child_counts(
    tmp_path: Path,
) -> None:
    reference = RuntimeMeasurementSnapshot.from_output_snapshot(
        _saved_outputs(tmp_path / "native", edges=False)
    )
    candidate = RuntimeMeasurementSnapshot.from_output_snapshot(
        _saved_outputs(tmp_path / "openhcs", edges=True)
    )
    assert runtime_measurement_equivalence(reference, candidate).is_equivalent


def test_relationship_endpoint_permutation_cannot_hide_in_equal_value_histograms(
    tmp_path: Path,
) -> None:
    reference = RuntimeMeasurementSnapshot.from_output_snapshot(
        _saved_outputs(tmp_path / "native", edges=False)
    )
    candidate = RuntimeMeasurementSnapshot.from_output_snapshot(
        _saved_outputs(tmp_path / "openhcs", edges=True, swapped=True)
    )
    assert not runtime_measurement_equivalence(reference, candidate).is_equivalent


def test_relationship_rows_must_agree_with_explicit_parent_measurements(
    tmp_path: Path,
) -> None:
    snapshot = _saved_outputs(tmp_path / "openhcs", edges=True)
    table = next(
        table for table in snapshot.tables if table.path.stem == "Relationships"
    )
    table.rows = tuple(
        tuple(
            "2" if index == 6 and row[7] == "1" and row[8] == "1" else value
            for index, value in enumerate(row)
        )
        for row in table.rows
    )
    with pytest.raises(ValueError, match="relationship|Relationship"):
        RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)


def test_ordinary_image_row_conflicts_remain_rejected(tmp_path: Path) -> None:
    root = tmp_path / "ordinary"
    root.mkdir()
    (root / "Image.csv").write_text("ImageNumber,Count_Nuclei\n1,2\n1,3\n")
    with pytest.raises(ValueError, match="conflicting observed values"):
        RuntimeMeasurementSnapshot.from_output_snapshot(
            RuntimeOutputSnapshot.from_output_root(root)
        )


@pytest.mark.parametrize(
    "mutation, message",
    [
        (
            lambda header, rows: (header, rows[:-1]),
            "Relationship edges disagree|reverse declarations",
        ),
        (lambda header, rows: (header, (*rows, rows[0])), "duplicate directed edges"),
        (
            lambda header, rows: (
                header,
                tuple(
                    tuple(
                        "12" if i == 5 and row[0] == "Child" else value
                        for i, value in enumerate(row)
                    )
                    for row in rows
                ),
            ),
            "reverse declarations",
        ),
        (
            lambda header, rows: (
                header,
                tuple(
                    tuple(
                        "neighbor_source" if i == 1 else value
                        for i, value in enumerate(row)
                    )
                    for row in rows
                ),
            ),
            "Unsupported exported relationship roles",
        ),
        (
            lambda header, rows: (
                header,
                tuple(
                    tuple("999" if i == 7 else value for i, value in enumerate(row))
                    for row in rows
                ),
            ),
            "absent child",
        ),
        (
            lambda header, rows: (
                header,
                tuple(
                    tuple("2.5" if i == 6 else value for i, value in enumerate(row))
                    for row in rows
                ),
            ),
            "nonnegative integers",
        ),
        (
            lambda header, rows: (
                header,
                tuple(
                    tuple("2.5" if i == 9 else value for i, value in enumerate(row))
                    for row in rows
                ),
            ),
            "slice count must be an integer",
        ),
        (
            lambda header, rows: (header[1:], tuple(row[1:] for row in rows)),
            "incomplete declaration",
        ),
        (lambda header, rows: (header, ()), "no determining declaration"),
    ],
)
def test_saved_edge_schema_and_coverage_rejects_malformed_inputs(
    tmp_path: Path, mutation, message: str
) -> None:
    snapshot = _saved_outputs(tmp_path / "openhcs", edges=True)
    table = next(
        table for table in snapshot.tables if table.path.stem == "Relationships"
    )
    table.header, table.rows = mutation(table.header, table.rows)
    with pytest.raises((ValueError, TypeError), match=message):
        RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)


def test_saved_relationship_counts_include_noncontiguous_zero_child_parents(
    tmp_path: Path,
) -> None:
    native = _saved_outputs(tmp_path / "native", edges=False)
    candidate = _saved_outputs(tmp_path / "openhcs", edges=True)
    for snapshot in (native, candidate):
        for table in snapshot.tables:
            table.rows = tuple(
                tuple(
                    (
                        "30"
                        if table.path.stem == "Cells" and i == 1 and value == "3"
                        else value
                    )
                    for i, value in enumerate(row)
                )
                for row in table.rows
            )
    a = RuntimeMeasurementSnapshot.from_output_snapshot(native)
    b = RuntimeMeasurementSnapshot.from_output_snapshot(candidate)
    assert (
        a.correlated_relationships is not None
        and b.correlated_relationships is not None
    )
    assert runtime_measurement_equivalence(a, b).is_equivalent


def test_snapshot_cache_retains_known_correlations_and_unknown_typed_scope(
    tmp_path: Path,
) -> None:
    known = RuntimeMeasurementSnapshot.from_output_snapshot(
        _saved_outputs(tmp_path / "saved", edges=True)
    )
    unknown = RuntimeMeasurementSnapshot(known.measurement_fact_counts)
    for snapshot in (known, unknown):
        restored = RuntimeMeasurementSnapshot.from_cache_payload(
            snapshot.to_cache_payload()
        )
        assert restored.measurement_fact_counts == snapshot.measurement_fact_counts
        assert restored.correlated_relationships == snapshot.correlated_relationships
    assert unknown.correlated_relationships is None
    assert known.correlated_relationships is not None


def test_cached_relationship_preserves_declared_slice_count_and_endpoint_axes() -> None:
    from openhcs.core.equivalence.keys import (
        RuntimeMeasurementFeatureKey,
        RuntimeMeasurementSubjectKey,
    )
    from openhcs.core.runtime_measurements import MeasurementScope
    from openhcs.core.runtime_relationships import (
        ObjectInstanceKey,
        ObjectInstanceRelationship,
    )

    key = RuntimeMeasurementFeatureKey(
        RuntimeMeasurementSubjectKey(MeasurementScope.RELATIONSHIP, "child"), "parent"
    )
    graph = ObjectInstanceRelationship(
        (ObjectInstanceKey(2, 0),), (ObjectInstanceKey(5, 1),), 2
    )
    snapshot = RuntimeMeasurementSnapshot({}, {key: graph})
    assert (
        RuntimeMeasurementSnapshot.from_cache_payload(
            snapshot.to_cache_payload()
        ).correlated_relationships
        == snapshot.correlated_relationships
    )


def test_saved_relationship_omitted_slice_count_preserves_optional_payload_contract(
    tmp_path: Path,
) -> None:
    snapshot = _saved_outputs(tmp_path / "saved", edges=True)
    table = next(
        table for table in snapshot.tables if table.path.stem == "Relationships"
    )
    table.header = table.header[:-1]
    table.rows = tuple(row[:-1] for row in table.rows)
    result = RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)
    assert result.correlated_relationships is not None


def test_saved_relationship_row_order_does_not_change_directed_correlation(
    tmp_path: Path,
) -> None:
    native = RuntimeMeasurementSnapshot.from_output_snapshot(
        _saved_outputs(tmp_path / "native", edges=False)
    )
    snapshot = _saved_outputs(tmp_path / "saved", edges=True)
    table = next(
        table for table in snapshot.tables if table.path.stem == "Relationships"
    )
    table.rows = table.rows[:4] + table.rows[4:][::-1]
    result = RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)
    assert runtime_measurement_equivalence(native, result).is_equivalent


def test_unparented_zero_edges_still_validate_actual_child_domain(
    tmp_path: Path,
) -> None:
    snapshot = _saved_outputs(tmp_path / "saved", edges=True)
    for table in snapshot.tables:
        if table.path.stem == "Cells":
            table.rows = tuple((*row[:2], "0") for row in table.rows)
        elif table.path.stem == "Nuclei":
            table.rows = tuple((*row[:2], "0") for row in table.rows)
        else:
            table.rows = tuple((*row[:6], "0", *row[7:]) for row in table.rows)
    result = RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)
    assert result.correlated_relationships is not None
    assert all(
        not graph.source_keys for graph in result.correlated_relationships.values()
    )
    table = next(
        table for table in snapshot.tables if table.path.stem == "Relationships"
    )
    table.rows = tuple((*row[:7], "999", *row[8:]) for row in table.rows)
    with pytest.raises(ValueError, match="absent child"):
        RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)


@pytest.mark.parametrize(
    "feature, identity",
    [
        ("Children_ Nuclei _Count", "Nuclei"),
        ("Children__Count", None),
        ("Children_Nuclei", None),
        (" children_Nuclei_Count", None),
    ],
)
def test_child_count_parser_and_core_declaration_share_original_grammar(
    feature: str, identity: str | None
) -> None:
    from openhcs.core.runtime_relationships import ChildCountFeatureDeclaration
    from openhcs.interop.cellprofiler.measurement_lookup import (
        CellProfilerChildCountFeatureParser,
    )

    assert ChildCountFeatureDeclaration.from_feature_name(feature) == identity
    parsed = CellProfilerChildCountFeatureParser().parse_feature(feature)
    assert (None if parsed is None else parsed.object_name) == identity


@pytest.mark.parametrize("swapped", (False, True))
def test_physical_inventory_consumes_redundant_edges_and_compares_exact_correlations(
    tmp_path: Path, swapped: bool
) -> None:
    from benchmark.matched_cellprofiler_batch import _require_compared_output_inventory
    from openhcs.core.runtime_exports import RuntimeExportObservation

    reference = _saved_outputs(tmp_path / "native", edges=False)
    candidate = _saved_outputs(tmp_path / "saved", edges=True, swapped=swapped)
    reference_exports = RuntimeExportObservation.from_output_root(tmp_path / "native")
    candidate_exports = RuntimeExportObservation.from_output_root(tmp_path / "saved")
    kwargs = dict(
        reference_files=frozenset((tmp_path / "native").iterdir()),
        candidate_files=frozenset((tmp_path / "saved").iterdir()),
        reference_exports=reference_exports,
        candidate_exports=candidate_exports,
        reference_snapshot=reference,
        candidate_snapshot=candidate,
    )
    if swapped:
        with pytest.raises(RuntimeError, match="correlations differ"):
            _require_compared_output_inventory(**kwargs)
    else:
        _require_compared_output_inventory(**kwargs)


@pytest.mark.parametrize(
    "parent_value, message",
    [("999", "absent parent endpoint"), ("2.5", "integral endpoint")],
)
def test_native_parent_rows_require_real_integral_parent_domain(
    tmp_path: Path, parent_value: str, message: str
) -> None:
    snapshot = _saved_outputs(tmp_path / "native", edges=False)
    table = next(table for table in snapshot.tables if table.path.stem == "Nuclei")
    table.rows = tuple((*row[:2], parent_value) for row in table.rows)
    with pytest.raises(ValueError, match=message):
        RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)


def test_native_child_count_permutation_cannot_hide_in_equal_histograms(
    tmp_path: Path,
) -> None:
    snapshot = _saved_outputs(tmp_path / "native", edges=False)
    table = next(table for table in snapshot.tables if table.path.stem == "Cells")
    table.rows = tuple((*row[:2], "0" if row[1] == "1" else "1") for row in table.rows)
    with pytest.raises(ValueError, match="disagree with.*children_nuclei_count"):
        RuntimeMeasurementSnapshot.from_output_snapshot(snapshot)


def test_snapshot_json_cache_retains_correlation_scope(tmp_path: Path) -> None:
    import json

    known = RuntimeMeasurementSnapshot.from_output_snapshot(
        _saved_outputs(tmp_path / "saved", edges=True)
    )
    for snapshot in (known, RuntimeMeasurementSnapshot(known.measurement_fact_counts)):
        restored = RuntimeMeasurementSnapshot.from_cache_payload(
            json.loads(json.dumps(snapshot.to_cache_payload()))
        )
        assert restored.correlated_relationships == snapshot.correlated_relationships
        assert restored.measurement_fact_counts == snapshot.measurement_fact_counts


@pytest.mark.parametrize("slice_index", (None, 0, 2))
def test_object_identity_owns_required_plane_admission(slice_index: int | None) -> None:
    from openhcs.core.runtime_relationships import ObjectInstanceKey

    key = ObjectInstanceKey(1, slice_index)
    if slice_index is None:
        with pytest.raises(ValueError, match="explicit image or slice identity"):
            key.required_slice_index()
    else:
        assert key.required_slice_index() == slice_index


def test_full_saved_comparison_cannot_admit_unknown_relationship_scope() -> None:
    unknown = RuntimeMeasurementSnapshot({})
    with pytest.raises(RuntimeError, match="requires known relationship correlations"):
        unknown.required_relationship_correlations()
    known = RuntimeMeasurementSnapshot({}, {})
    assert known.required_relationship_correlations() is known.correlated_relationships
