"""Kernel feature names over saved CellProfiler-format tables, for equivalence tests.

Saved tables number samples in ``ImageNumber``, name their sample and run
tables ``Image`` and ``Experiment`` and spell relationships ``Parent_<object>``
and ``Children_<object>_Count``; other feature names keep the kernel's plain
canonicalization, so comparisons see the files as written.
"""

from __future__ import annotations

from openhcs.core.equivalence.policy import RuntimeEquivalencePolicy
from openhcs.core.measurement_dialect import PlainMeasurementDialect
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    RuntimeMeasurementRowIdentityContract,
)
from openhcs.interop.cellprofiler.measurement_dialect import (
    CELLPROFILER_MEASUREMENT_DIALECT,
)
from openhcs.interop.cellprofiler.measurement_scope import CELLPROFILER_SCOPE_NAMES


class SavedOutputDialect(PlainMeasurementDialect):
    dialect_name = None
    row_identity_contract = RuntimeMeasurementRowIdentityContract(
        fallback_sample_fields=frozenset({"image_number", "image_id"}),
        sample_number_field="image_number",
    )

    def scope_name(self, scope: MeasurementScope) -> str:
        return CELLPROFILER_SCOPE_NAMES.get(scope, scope.value)

    def parent_reference_feature_name(self, parent_object_name: str) -> str:
        return CELLPROFILER_MEASUREMENT_DIALECT.parent_reference_feature_name(
            parent_object_name
        )

    def parent_reference_object_name(self, feature_name: str) -> str | None:
        return CELLPROFILER_MEASUREMENT_DIALECT.parent_reference_object_name(
            feature_name
        )

    def child_count_feature_name(self, child_object_name: str) -> str:
        return CELLPROFILER_MEASUREMENT_DIALECT.child_count_feature_name(
            child_object_name
        )


SAVED_OUTPUT_DIALECT = SavedOutputDialect.shared()
SAVED_OUTPUT_POLICY = RuntimeEquivalencePolicy(measurement_dialect=SAVED_OUTPUT_DIALECT)
