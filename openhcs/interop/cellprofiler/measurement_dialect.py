"""CellProfiler's measurement dialect: how its rows and features are named."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from types import MappingProxyType

from openhcs.core.equivalence.policy import (
    NonNegativeFloat,
    RuntimeEquivalencePolicy,
)
from openhcs.core.measurement_dialect import (
    MeasurementDialect,
    RuntimeMeasurementFeatureLookup,
    RuntimeMeasurementSourceNameEncoding,
)
from openhcs.core.runtime_measurements import (
    MeasurementRowAxisField,
    MeasurementScope,
    ObjectCoreMeasurementFeature,
    RuntimeMeasurementRowIdentityContract,
    RuntimeMeasurementFeatureDeclaration,
)
from openhcs.interop.cellprofiler import (
    measurement_semantic_profiles as _measurement_semantic_profiles,  # noqa: F401
)
from openhcs.interop.cellprofiler.database_column_dialect import (
    CellProfilerDatabaseColumnDialect,
    CellProfilerObjectCoreMeasurementFeature,
)
from openhcs.interop.cellprofiler.measurement_scope import CELLPROFILER_SCOPE_NAMES
from openhcs.interop.cellprofiler.measurement_lookup import (
    ChildCountFeatureDeclaration,
    DirectParentReferenceFeatureDeclaration,
    DirectParentReferenceMeasurementFeature,
    child_count_feature_child_name,
)
from openhcs.interop.cellprofiler.module_declarations import (
    CellProfilerModule,
)


class CellProfilerSpatialGridMeasurementFeature(Enum):
    """CellProfiler field names for canonical spatial-grid geometry."""

    COLUMNS = ("columns", "Columns")
    ROWS = ("rows", "Rows")
    X_ORIGIN = ("x_origin", "XLocationOfLowestXSpot")
    X_SPACING = ("x_spacing", "XSpacing")
    Y_ORIGIN = ("y_origin", "YLocationOfLowestYSpot")
    Y_SPACING = ("y_spacing", "YSpacing")

    def __init__(self, canonical_field_name: str, cellprofiler_field_name: str) -> None:
        self.canonical_field_name = canonical_field_name
        self.cellprofiler_field_name = cellprofiler_field_name

    @classmethod
    def render(cls, grid_name: str, field_name: str) -> str:
        """Render the exact CellProfiler feature for one canonical grid field."""

        matching = tuple(
            feature for feature in cls if feature.canonical_field_name == field_name
        )
        if len(matching) != 1:
            raise ValueError(
                "CellProfiler spatial-grid measurement does not declare canonical "
                f"field {field_name!r}."
            )
        return f"DefinedGrid_{grid_name}_{matching[0].cellprofiler_field_name}"


CELLPROFILER_OBJECT_NUMBER_FEATURE_PARTS = tuple(
    part.casefold()
    for part in CellProfilerObjectCoreMeasurementFeature.OBJECT_NUMBER.value.split("_")
)
CELLPROFILER_CORE_MEASUREMENT_FEATURE_PART_ALIASES = MappingProxyType(
    {
        CELLPROFILER_OBJECT_NUMBER_FEATURE_PARTS: ("object", "number"),
        **{
            tuple(feature.value.split("_")): tuple(feature.value.split("_"))
            for feature in (
                ObjectCoreMeasurementFeature.CENTER_X,
                ObjectCoreMeasurementFeature.CENTER_Y,
                ObjectCoreMeasurementFeature.CENTER_Z,
            )
        },
    }
)


class CellProfilerMeasurementDialect(MeasurementDialect):
    """CellProfiler's measurement names: ImageNumber, Image/Experiment tables,
    category prefixes and feature rewrites declared by the module family."""

    dialect_name = "cellprofiler"
    row_identity_contract = RuntimeMeasurementRowIdentityContract(
        fallback_sample_fields=frozenset({"image_number", "image_id"}),
        sample_number_field="image_number",
        object_identity_output_field=MeasurementRowAxisField.OBJECT_NUMBER.value,
        object_identity_fields=(
            "_".join(CELLPROFILER_OBJECT_NUMBER_FEATURE_PARTS),
            *MeasurementRowAxisField.object_id_field_names(),
        ),
    )
    threshold_qualifier_tokens = frozenset(
        {
            "w",
            "weighted",
            "variance",
            "entropy",
            "foreground",
            "background",
            "classes",
            "class",
        }
    )
    source_qualifier_prefix_tokens = frozenset({"crop", "orig", "raw", "image"})
    source_qualifier_suffix_tokens = frozenset(
        {"red", "green", "blue", "gray", "grey", "dna", "gfp", "rfp"}
    )

    def scope_name(self, scope: MeasurementScope) -> str:
        return CELLPROFILER_SCOPE_NAMES.get(scope, scope.value.title())

    def category_prefix_declarations(self):
        return CellProfilerModule.measurement_category_prefix_declarations()

    def primary_category_prefix_declarations(self):
        return CellProfilerModule.primary_measurement_category_prefix_declarations()

    def feature_part_alias_declarations(self):
        return {
            **CELLPROFILER_CORE_MEASUREMENT_FEATURE_PART_ALIASES,
            **CellProfilerModule.measurement_feature_part_rewrite_declarations(),
        }

    def alternative_feature_part_alias_declarations(self):
        return CellProfilerModule.alternative_measurement_feature_part_aliases()

    def source_qualified_feature_family_declarations(self):
        return CellProfilerModule.source_qualified_measurement_feature_family_parts()

    def source_feature_prefix_declarations(self):
        return CellProfilerModule.measurement_source_feature_prefix_declarations()

    def calculated_feature_prefix_declarations(self):
        return CellProfilerModule.calculated_measurement_feature_prefix_declarations()

    def directional_pair_feature_alias_declarations(self):
        return CellProfilerModule.directional_pair_feature_alias_declarations()

    def scale_qualified_feature_prefix_declarations(self):
        return (
            CellProfilerModule.scale_qualified_measurement_feature_prefix_declarations()
        )

    def pair_correlation_feature_name_declaration(self):
        return CellProfilerModule.pair_correlation_feature_name_declaration()

    def pair_regression_slope_feature_name_declaration(self):
        return CellProfilerModule.pair_regression_slope_feature_name_declaration()

    def undirected_pair_feature_name_declarations(self):
        return CellProfilerModule.undirected_pair_feature_name_declarations()

    def threshold_sensitive_pair_feature_name_declarations(self):
        return CellProfilerModule.threshold_sensitive_pair_feature_name_declarations()

    def numbered_feature_prefix_alias_declarations(self):
        return (
            CellProfilerModule.numbered_measurement_feature_prefix_alias_declarations()
        )

    def non_measurement_field_prefix_declarations(self):
        return CellProfilerDatabaseColumnDialect.structural_field_prefixes()

    def feature_relation_declarations(self):
        return CellProfilerModule.measurement_feature_relation_declarations()

    def measurement_feature_marker_declarations(self, key: object):
        return CellProfilerModule.measurement_feature_marker_types_for_key(key, self)

    def indexed_descriptor_suffix_width(self, feature_parts: tuple[str, ...]):
        return RuntimeMeasurementFeatureDeclaration.indexed_suffix_token_width_for(
            feature_parts
        )

    def source_name_encoding(
        self,
        scope: MeasurementScope,
    ) -> RuntimeMeasurementSourceNameEncoding:
        if scope in (MeasurementScope.SAMPLE, MeasurementScope.OBJECT):
            return RuntimeMeasurementSourceNameEncoding.FEATURE_SUFFIX
        return RuntimeMeasurementSourceNameEncoding.SEPARATE_KEY

    def query_object_name(
        self,
        lookup: RuntimeMeasurementFeatureLookup,
        object_name: str | None,
    ) -> str | None:
        """Child-count features live on the parent's rows, under no object."""
        if child_count_feature_child_name(lookup.feature_name) is not None:
            return None
        return object_name

    def render_spatial_grid_feature(
        self,
        grid_name: str,
        normalized_grid_name: str,
        normalized_field_name: str,
    ) -> str:
        del normalized_grid_name
        return CellProfilerSpatialGridMeasurementFeature.render(
            grid_name,
            normalized_field_name,
        )

    def parent_reference_feature_name(self, parent_object_name: str) -> str:
        return DirectParentReferenceFeatureDeclaration.feature_name(
            DirectParentReferenceMeasurementFeature(parent_object_name)
        )

    def parent_reference_object_name(self, feature_name: str) -> str | None:
        identity = DirectParentReferenceFeatureDeclaration.from_feature_name(feature_name)
        return None if identity is None else identity.parent_object_name

    def child_count_feature_name(self, child_object_name: str) -> str:
        return ChildCountFeatureDeclaration.feature_name(child_object_name)


class CellProfilerModuleMeasurementDialect(CellProfilerMeasurementDialect):
    """The CellProfiler dialect narrowed to the declarations of one module."""

    dialect_name = None

    def __init__(self, owner: type[CellProfilerModule]) -> None:
        super().__init__()
        self.owner = owner

    def category_prefix_declarations(self):
        return self.owner.measurement_category_prefixes

    def feature_part_alias_declarations(self):
        return {
            **CELLPROFILER_CORE_MEASUREMENT_FEATURE_PART_ALIASES,
            **self.owner.declared_measurement_feature_part_rewrites(),
        }

    def alternative_feature_part_alias_declarations(self):
        return self.owner.measurement_feature_part_aliases

    def source_qualified_feature_family_declarations(self):
        return self.owner.declared_source_qualified_measurement_feature_family_parts()


CELLPROFILER_MEASUREMENT_DIALECT = CellProfilerMeasurementDialect.shared()


@lru_cache(maxsize=None)
def cellprofiler_dialect_for_measurement_owner(
    owner: type[CellProfilerModule] | None,
) -> CellProfilerMeasurementDialect:
    """Return the dialect narrowed to one recorded table owner."""
    owner_name = getattr(owner, "module_name", None)
    if (
        not isinstance(owner_name, str)
        or dict.get(CellProfilerModule.__registry__, owner_name) is not owner
    ):
        return CELLPROFILER_MEASUREMENT_DIALECT
    return CellProfilerModuleMeasurementDialect(owner)


@dataclass(frozen=True, slots=True)
class CellProfilerEquivalencePolicy(RuntimeEquivalencePolicy):
    """Equivalence policy with CellProfiler's Zernike-descriptor tolerances."""

    allow_unstable_zernike_descriptors: bool = False
    zernike_descriptor_magnitude_abs_tolerance: NonNegativeFloat = 1e-6
    zernike_descriptor_phase_abs_tolerance: NonNegativeFloat = 0.35
    zernike_descriptor_rel_tolerance: NonNegativeFloat = 0.0

    @classmethod
    def for_policy(
        cls, policy: RuntimeEquivalencePolicy
    ) -> "CellProfilerEquivalencePolicy":
        """The CellProfiler tolerances a policy carries; a kernel policy is strict."""
        return policy if isinstance(policy, cls) else cls()


def cellprofiler_runtime_equivalence_policy(
    **overrides: object,
) -> CellProfilerEquivalencePolicy:
    """Build a runtime-equivalence policy with CellProfiler measurement dialect."""
    overrides.setdefault("measurement_dialect", CELLPROFILER_MEASUREMENT_DIALECT)
    overrides.setdefault("numeric_abs_tolerance", 1e-06)
    overrides.setdefault("numeric_rel_tolerance", 1e-06)
    overrides.setdefault("threshold_entropy_abs_tolerance", 0.04)
    overrides.setdefault("allow_tie_sensitive_location_mismatches", True)
    overrides.setdefault("allow_sparse_object_boundary_jitter", True)
    overrides.setdefault("allow_unstable_shape_descriptors", True)
    overrides.setdefault("allow_unstable_zernike_descriptors", True)
    overrides.setdefault("shape_descriptor_abs_tolerance", 1e-06)
    overrides.setdefault("zernike_descriptor_magnitude_abs_tolerance", 1e-06)
    overrides.setdefault("object_boundary_jitter_abs_tolerance", 5.0)
    overrides.setdefault("object_boundary_jitter_max_unstable_values", 50)
    overrides.setdefault("object_boundary_jitter_max_unstable_fraction", 0.02)
    overrides.setdefault("object_boundary_jitter_aggregate_abs_tolerance", 1.5)
    overrides.setdefault("image_abs_tolerance", 1e-06)
    overrides.setdefault("image_rel_tolerance", 1e-06)
    return CellProfilerEquivalencePolicy(**overrides)
