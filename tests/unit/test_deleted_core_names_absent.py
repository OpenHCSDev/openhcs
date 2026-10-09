"""Guard: dead core and runtime names removed by surface D2 stay removed."""

from __future__ import annotations

import ast
from dataclasses import fields
from pathlib import Path

import openhcs
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.orchestrator.execution_result import ExecutionStatus
from openhcs.core.pipeline import function_contracts

OPENHCS_ROOT = Path(openhcs.__file__).parent

DELETED_NAMES = frozenset(
    {
        # core/utils.py thread tracking and natural sorting
        "get_thread_activity",
        "get_active_threads",
        "clear_thread_activity",
        "track_thread_activity",
        "analyze_thread_activity",
        "print_thread_activity_report",
        "natural_sort_key",
        "natural_sort",
        "natural_sort_inplace",
        "WellPatternConstants",
        # metadata cache and source bindings
        "get_metadata_cache",
        "_metadata_cache_service",
        "SourceRuntimePathLookup",
        "metadata_source_text",
        # callable-contract projections restated beside CallableContract
        "special_input_parameters_from_callable",
        "special_input_names_from_callable",
        "image_payload_consumption_from_callable",
        "runtime_bound_parameter_names_from_callable",
        "normalize_pattern",
        "special_outputs",
        # archived runtime-export readers
        "_restore_legacy_axis_expectation",
        # measurement and equivalence helpers
        "specific_measurement_feature_candidates",
        "ordered_measurement_source_candidates",
        "measurement_value_indexes_for_object_feature_batch",
        "measurement_feature_candidates",
        "matching_measurement_field",
        "ProjectedMeasurementRows",
        "measurement_row_identity_role",
        "measurement_row_field_value",
        "carries_measurement_row_semantics",
        "runtime_measurement_tables_for_object",
        "runtime_measurement_tables_for_scope",
        "runtime_relationship",
        "measurement_table_slice_indices",
        "ObjectMeasurementSliceValueRow",
        "RuntimeMeasurementCellPresence",
        "RuntimeMeasurementValuePresence",
        "RuntimeMeasurementRowIdentityOrMissing",
        "RuntimeMeasurementIndexedQualifierCache",
        "runtime_measurement_identity_field_matches",
        "RuntimeSnapshotLongFormMeasurementFactProjector",
        "is_wide_measurement_table",
    }
)


def _referenced_names(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.Name):
            names.add(node.id)
        elif isinstance(node, ast.Attribute):
            names.add(node.attr)
        elif isinstance(node, ast.alias):
            names.add(node.name.rsplit(".", 1)[-1])
            if node.asname is not None:
                names.add(node.asname)
    return names


def test_deleted_core_names_stay_absent_from_openhcs() -> None:
    violations = sorted(
        f"{path.relative_to(OPENHCS_ROOT.parent)}: {name}"
        for path in OPENHCS_ROOT.rglob("*.py")
        for name in _referenced_names(ast.parse(path.read_text(encoding="utf-8")))
        & DELETED_NAMES
    )
    assert violations == []


def test_deleted_core_members_stay_absent() -> None:
    assert "step_type" not in {field.name for field in fields(CompiledStepPlan)}
    assert "PENDING" not in ExecutionStatus.__members__
    assert not hasattr(function_contracts, "validate_artifact_input_parameter_bindings")
