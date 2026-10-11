"""Nominal runtime measurement table values."""

from __future__ import annotations

from collections.abc import Iterable
from functools import lru_cache
from dataclasses import dataclass, field

from openhcs.core.artifacts.payloads import NamedArtifactPayload
from openhcs.core.runtime_tabular_values import (
    ColumnarRows,
    FieldSpec,
    MeasurementObjectRowIdentity,
)
from openhcs.core.source_image_provenance import (
    SourceImageProvenance,
    SourceImageProvenanceFields,
)

from abc import ABC
from abc import abstractmethod
from collections.abc import Mapping
from collections.abc import Sequence
from enum import Enum
from metaclass_registry import AutoRegisterMeta
from openhcs.core.alias_property import AliasProperty
from metaclass_registry.strategies import str_enum_member_with_payload
from openhcs.core.runtime_identifier import normalize_runtime_identifier
from openhcs.core.runtime_object_label_domains import ObjectLabelDomain
from typing import Any
from typing import ClassVar
import math
import numpy as np
import re
from openhcs.core.axes import AxisFamily
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.source_spatial_domain import (
    SourceSpatialDomain,
    VolumeSourceSpatialDomain,
)


@dataclass(slots=True, kw_only=True)
class MeasurementTable(
    SourceImageProvenanceFields,
    NamedArtifactPayload,
    ColumnarRows,
):
    """Native OpenHCS measurement table value."""

    name: str
    rows: ColumnarRows
    source_image_name: str | None = None
    subject: MeasurementSubject
    measurement_feature_owner: type[RuntimeMeasurementFeatureOwner] | None = None

    @property
    def columns(self) -> Any:
        return self.rows.columns

    @property
    def fields(self) -> tuple[FieldSpec, ...]:
        return self.rows.fields

    @property
    def object_row_identity(self) -> MeasurementObjectRowIdentity | None:
        return self.rows.object_row_identity

    @property
    def covers_declared_object_measurement_domain(self) -> bool:
        return self.rows.covers_declared_object_measurement_domain

    def iter_row_mappings(self) -> Iterable[Mapping[str, object]]:
        return self.rows.iter_row_mappings()

    def __post_init__(self, *source_provenance_values: object) -> None:
        self.absorb_explicit_source_provenance(source_provenance_values)
        self.normalize_source_provenance_fields()
        self.require_name()
        if self.source_image_name == "":
            raise ValueError("MeasurementTable.source_image_name cannot be empty.")
        if not isinstance(self.subject, MeasurementSubject):
            raise TypeError("MeasurementTable.subject requires MeasurementSubject.")
        if self.measurement_feature_owner is not None and (
            not isinstance(self.measurement_feature_owner, type)
            or not issubclass(
                self.measurement_feature_owner,
                RuntimeMeasurementFeatureOwner,
            )
        ):
            raise TypeError(
                "MeasurementTable.measurement_feature_owner requires a "
                "RuntimeMeasurementFeatureOwner type."
            )
        if not isinstance(self.rows, ColumnarRows):
            raise TypeError(
                f"MeasurementTable {self.name!r} requires schema-bearing "
                "ColumnarRows, "
                f"got {type(self.rows).__name__}."
            )
        self.rows.validate_fields()
        self.validate_runtime_slice_axis()

    def runtime_slice_row_domain(self) -> tuple[int, ...] | None:
        """Return the runtime-slice indices these rows carry, if they carry the axis."""
        return MeasurementTable.shared_row_axis_domain(
            self.name, (self,), MeasurementRowAxisField.SLICE_INDEX
        )

    def runtime_slice_count(self) -> int | None:
        if self.runtime_slice_row_domain() is None:
            return None
        if self.source_provenance.source_plane_count > 0:
            return self.source_provenance.source_plane_count
        if self.source_provenance.addressable:
            return None
        from openhcs.core.runtime_slice_projection import (
            RuntimeSliceProjectionDeclarationError,
        )

        raise RuntimeSliceProjectionDeclarationError(
            "Runtime-slice measurement table requires declared source-plane "
            "provenance; row fields and row ordering cannot declare its axis."
        )

    def value_for_slice(self, context: Any) -> "MeasurementTable":
        """Select the rows of one runtime slice."""

        selects_slice_rows = (
            context.axis.one_plane_per_runtime_slice
            and self.runtime_slice_row_domain() is not None
        )
        if not selects_slice_rows:
            return self
        from openhcs.core.runtime_artifact_queries import (
            MeasurementTableAxisProjection,
        )

        return MeasurementTableAxisProjection(
            axis=MeasurementRowAxisField.SLICE_INDEX,
            value=context.require_plane_index(),
            table=self,
        ).apply()

    def validate_runtime_slice_axis(self) -> None:
        """Require non-negative values on the canonical runtime slice axis."""
        axis = MeasurementRowAxisField.SLICE_INDEX
        slice_field = axis.value
        if slice_field not in {field.name for field in self.rows.fields}:
            return
        for slice_index in measurement_axis_integer_domain(
            self.rows.column_values(slice_field),
            axis,
        ):
            if slice_index < 0:
                raise ValueError(
                    f"MeasurementTable {self.name!r} has negative slice_index "
                    f"{slice_index}."
                )

    @property
    def runtime_semantic_id(self) -> str:
        """Return the exact semantic partition represented by this table."""

        feature_owner = self.measurement_feature_owner
        feature_owner_name = (
            None
            if feature_owner is None
            else f"{feature_owner.__module__}.{feature_owner.__qualname__}"
        )
        return repr(
            (
                self.subject.identity_token,
                feature_owner_name,
                self.source_image_name,
            )
        )

    @classmethod
    def join(cls, name: str, tables: tuple[MeasurementTable, ...]) -> MeasurementTable:
        """Concatenate tables with one exact subject, feature owner and image owner."""
        cls._require_join(name, tables)
        if len(tables) == 1:
            return tables[0]
        subjects = tuple(dict.fromkeys(table.subject for table in tables))
        if len(subjects) != 1:
            raise ValueError(
                "Measurement table unions require one exact nominal subject; "
                f"got {subjects!r}."
            )
        owners = tuple(
            dict.fromkeys(table.measurement_feature_owner for table in tables)
        )
        if len(owners) != 1:
            raise ValueError(
                "Measurement table unions require one exact nominal measurement "
                f"feature owner; got {owners!r}."
            )
        source_names = tuple(dict.fromkeys(table.source_image_name for table in tables))
        if len(source_names) != 1:
            raise ValueError(
                "Measurement table unions require one exact source-image owner; "
                f"got {source_names!r}."
            )
        from openhcs.core.measurement_row_materialization import (
            ConcatenatedColumnarRows,
        )

        return cls(
            name=name,
            rows=ConcatenatedColumnarRows(tuple(table.rows for table in tables)),
            source_image_name=source_names[0],
            subject=subjects[0],
            measurement_feature_owner=owners[0],
            source_provenance=cls.joined_source_provenance(name, tables),
        )

    @classmethod
    def join_artifact(
        cls, name: str, tables: tuple[MeasurementTable, ...]
    ) -> MeasurementTable:
        """Re-own mixed subject rows as one lossless artifact-level export table."""
        cls._require_join(name, tables)
        from openhcs.core.measurement_row_materialization import (
            ConcatenatedColumnarRows,
            MeasurementRowOwnership,
        )

        return cls(
            name=name,
            rows=ConcatenatedColumnarRows(
                tuple(
                    MeasurementRowOwnership(
                        object_name=table.subject.object_name,
                        source_image_name=(
                            table.source_image_name or table.subject.source_image_name
                        ),
                    ).annotate_rows(table.rows)
                    for table in tables
                )
            ),
            subject=MeasurementSubject(MeasurementScope.ARTIFACT, name),
            source_provenance=cls.joined_source_provenance(name, tables),
        )

    @staticmethod
    def _require_join(name: str, tables: tuple[MeasurementTable, ...]) -> None:
        if not name:
            raise ValueError("MeasurementTable join name cannot be empty.")
        if not tables:
            raise ValueError("MeasurementTable join tables cannot be empty.")

    @classmethod
    def joined_source_provenance(
        cls, name: str, tables: tuple[MeasurementTable, ...]
    ) -> SourceImageProvenance:
        """Compose exact table provenance on its declared runtime-slice axis."""
        cls._require_join(name, tables)
        if len(tables) == 1:
            return tables[0].source_provenance
        slice_axis = MeasurementRowAxisField.SLICE_INDEX
        table_domains = cls._row_axis_domains(name, tables, slice_axis)
        if table_domains is None:
            sources = tuple(table.source_provenance for table in tables)
            if not any(source.has_values for source in sources):
                return SourceImageProvenance()
            return SourceImageProvenance.stack(
                tuple(
                    (
                        source.for_source_plane(0)
                        if source.source_plane_count == 1
                        else source
                    )
                    for source in sources
                ),
                scalar_sources=sources,
            )
        axis_domain = tuple(
            sorted({value for domain in table_domains for value in domain})
        )
        declared_plane_counts = tuple(
            table.source_provenance.source_plane_count
            for table in tables
            if table.source_provenance.source_plane_count > 0
        )
        distinct_plane_counts = tuple(dict.fromkeys(declared_plane_counts))
        if len(distinct_plane_counts) > 1:
            raise ValueError(
                f"Measurement table union {name!r} cannot align declared "
                f"source-plane counts {distinct_plane_counts!r}."
            )
        axis_size = (
            distinct_plane_counts[0] if distinct_plane_counts else max(axis_domain) + 1
        )
        if max(axis_domain) >= axis_size:
            raise ValueError(
                f"Measurement table union {name!r} declares "
                f"{slice_axis.value}={max(axis_domain)} beyond its source-plane "
                f"axis of size {axis_size}."
            )
        for table, domain in zip(tables, table_domains, strict=True):
            provenance = table.source_provenance
            if (
                provenance.source_plane_count == 0
                and provenance.has_values
                and len(domain) > 1
            ):
                raise ValueError(
                    f"Measurement table {table.name!r} carries scalar source "
                    f"provenance for multiple {slice_axis.value} values {domain!r}."
                )
        planes: list[SourceImageProvenance] = []
        for plane_index in range(axis_size):
            sources = tuple(
                (
                    table.source_provenance.for_source_plane(plane_index)
                    if table.source_provenance.source_plane_count > 0
                    else table.source_provenance
                )
                for table, domain in zip(tables, table_domains, strict=True)
                if table.source_provenance.source_plane_count > 0
                or domain == (plane_index,)
            )
            if not sources:
                raise ValueError(
                    f"Measurement table union {name!r} has no declared "
                    f"source provenance for {slice_axis.value}={plane_index}."
                )
            planes.append(
                sources[0]
                if len(sources) == 1
                else (
                    SourceImageProvenance.bundle(
                        sources
                    ).with_runtime_planes_as_contributors()
                    if any(source.has_values for source in sources)
                    else SourceImageProvenance()
                )
            )
        return (
            SourceImageProvenance.stack(tuple(planes))
            if any(plane.has_values for plane in planes)
            else SourceImageProvenance()
        )

    @classmethod
    def shared_row_axis_domain(
        cls,
        name: str,
        tables: tuple[MeasurementTable, ...],
        axis: MeasurementRowAxisField,
    ) -> tuple[int, ...] | None:
        """Return the exact joined row-axis domain, or None for axisless rows."""
        cls._require_join(name, tables)
        domains = cls._row_axis_domains(name, tables, axis)
        if domains is None:
            return None
        return tuple(sorted({value for domain in domains for value in domain}))

    @staticmethod
    def _row_axis_domains(
        name: str, tables: tuple[MeasurementTable, ...], axis: MeasurementRowAxisField
    ) -> tuple[tuple[int, ...], ...] | None:
        from openhcs.core.measurement_row_materialization import (
            MeasurementRowsAxisProjection,
        )

        projections = tuple(
            MeasurementRowsAxisProjection.from_rows(table.rows) for table in tables
        )
        declarations = tuple(
            projection.declares_axis_field(axis)
            or any(field.name == axis.value for field in table.rows.fields)
            for table, projection in zip(tables, projections, strict=True)
        )
        if not any(declarations):
            return None
        domains = tuple(
            projection.present_axis_values(axis.value) for projection in projections
        )
        if not any(domains):
            return None
        for table, projection, domain in zip(tables, projections, domains, strict=True):
            if projection.has_rows and not domain:
                raise ValueError(
                    f"Measurement table union {name!r} mixes declared and "
                    f"axisless {axis.value!r} row domains; table {table.name!r} "
                    "declares no concrete axis value."
                )
        return domains


@dataclass(frozen=True, slots=True)
class ObjectLabelMeasurementValues:
    """Numeric measurements bound to explicit object-label identities."""

    object_ids: tuple[int, ...]
    values: np.ndarray

    def __post_init__(self) -> None:
        object_ids = ObjectLabelDomain._normalize_ids(
            self.object_ids, "ObjectLabelMeasurementValues.object_ids"
        )
        values = np.asarray(self.values, dtype=np.float64).reshape(-1)
        if len(object_ids) != values.size:
            raise ValueError(
                f"ObjectLabelMeasurementValues requires one value per object ID, got {len(object_ids)} IDs and {values.size} values."
            )
        object.__setattr__(self, "object_ids", object_ids)
        object.__setattr__(self, "values", values)

    @classmethod
    def from_label_indexed_values(
        cls, object_ids: Iterable[int], values: Any
    ) -> "ObjectLabelMeasurementValues":
        """Bind dense label-indexed values where index ``label_id - 1``."""
        normalized_ids = ObjectLabelDomain._normalize_ids(
            tuple(object_ids), "ObjectLabelMeasurementValues.object_ids"
        )
        source_values = np.asarray(values, dtype=np.float64).reshape(-1)
        bound_values = np.array(
            [
                (
                    source_values[object_id - 1]
                    if object_id - 1 < source_values.size
                    else np.nan
                )
                for object_id in normalized_ids
            ],
            dtype=np.float64,
        )
        return cls(normalized_ids, bound_values)

    @classmethod
    def from_positional_values(
        cls, object_ids: Iterable[int], values: Any
    ) -> "ObjectLabelMeasurementValues":
        """Bind values that are already ordered like ``object_ids``."""
        normalized_ids = ObjectLabelDomain._normalize_ids(
            tuple(object_ids), "ObjectLabelMeasurementValues.object_ids"
        )
        source_values = np.asarray(values, dtype=np.float64).reshape(-1)
        bound_values = np.full(len(normalized_ids), np.nan, dtype=np.float64)
        copied = min(source_values.size, bound_values.size)
        if copied:
            bound_values[:copied] = source_values[:copied]
        return cls(normalized_ids, bound_values)

    @classmethod
    def from_value_mapping(
        cls, object_ids: Iterable[int], values_by_object_id: Mapping[int, float]
    ) -> "ObjectLabelMeasurementValues":
        """Bind sparse object-id keyed values to an explicit object domain."""
        normalized_ids = ObjectLabelDomain._normalize_ids(
            tuple(object_ids), "ObjectLabelMeasurementValues.object_ids"
        )
        return cls(
            normalized_ids,
            np.array(
                [
                    float(values_by_object_id.get(object_id, np.nan))
                    for object_id in normalized_ids
                ],
                dtype=np.float64,
            ),
        )

    def __len__(self) -> int:
        return len(self.object_ids)

    def ids_within_limits(
        self,
        *,
        min_value: float | None,
        max_value: float | None,
        use_minimum: bool,
        use_maximum: bool,
    ) -> tuple[int, ...]:
        """Return object IDs whose finite values satisfy configured bounds."""
        if not self.object_ids:
            return ()
        hits = np.isfinite(self.values)
        if use_minimum and min_value is not None:
            hits[self.values < min_value] = False
        if use_maximum and max_value is not None:
            hits[self.values > max_value] = False
        return tuple(
            (
                object_id
                for object_id, hit in zip(self.object_ids, hits, strict=True)
                if bool(hit)
            )
        )

    def extremum_id(self, *, keep_max: bool) -> int | None:
        """Return the object ID with the finite minimum or maximum value."""
        if not self.object_ids:
            return None
        finite_indexes = np.flatnonzero(np.isfinite(self.values))
        if finite_indexes.size == 0:
            return None
        finite_values = self.values[finite_indexes]
        selected_index = finite_indexes[
            int(np.argmax(finite_values) if keep_max else np.argmin(finite_values))
        ]
        return self.object_ids[int(selected_index)]

    def dense_label_indexed(
        self, *, max_label: int | None = None, fill_value: float = np.nan
    ) -> np.ndarray:
        """Return values as a dense ``label_id - 1`` indexed vector."""
        largest_id = max(self.object_ids, default=0)
        output_size = max(largest_id, int(max_label or 0))
        output = np.full(output_size, fill_value, dtype=np.float64)
        for object_id, value in zip(self.object_ids, self.values, strict=True):
            output[object_id - 1] = value
        return output


class MeasurementScope(str, Enum):
    """Semantic entity scope for measurement rows."""

    def __new__(
        cls,
        value: str,
        requires_subject_name: bool = False,
    ):
        obj = str.__new__(cls, value)
        obj._value_ = value
        obj._requires_subject_name = requires_subject_name
        return obj

    ARTIFACT = ("artifact", False)
    SAMPLE = ("sample", True)
    OBJECT = ("object", True)
    RELATIONSHIP = ("relationship", True)
    RUN = ("run", False)
    requires_subject_name = AliasProperty[bool]("_requires_subject_name")


@dataclass(frozen=True, slots=True)
class MeasurementScopeSelection:
    """A closed set of measurement scopes selected for one runtime operation."""

    scopes: frozenset[MeasurementScope]

    def __post_init__(self) -> None:
        scopes = frozenset(
            (
                MeasurementScope(
                    scope,
                )
                for scope in self.scopes
            )
        )
        if not scopes:
            raise ValueError("MeasurementScopeSelection.scopes cannot be empty.")
        object.__setattr__(self, "scopes", scopes)

    @classmethod
    def of(cls, *scopes: MeasurementScope | str) -> "MeasurementScopeSelection":
        """Return a selection for one or more measurement scopes."""
        return cls(
            frozenset(
                (
                    MeasurementScope(
                        scope,
                    )
                    for scope in scopes
                )
            )
        )

    def includes(self, scope: MeasurementScope | str) -> bool:
        """Return whether this selection includes one semantic scope."""
        return (
            MeasurementScope(
                scope,
            )
            in self.scopes
        )

    def includes_all(self, *scopes: MeasurementScope | str) -> bool:
        """Return whether this selection includes every supplied semantic scope."""
        return all((self.includes(scope) for scope in scopes))


class RuntimeMeasurementFeatureRelation(ABC):
    """Polymorphic relation declared by a runtime measurement feature member."""

    @abstractmethod
    def source_family_names(
        self, source_feature: "RuntimeMeasurementFeature"
    ) -> tuple[str, ...]:
        """Return feature-family names that select the relation source."""

    @abstractmethod
    def target_family_name(
        self,
        source_feature: "RuntimeMeasurementFeature",
        source_family_name: str,
        feature_type: type["RuntimeMeasurementFeature"],
    ) -> str | None:
        """Return the target family for one selected source family."""


class RuntimeMeasurementFeatureOwner(ABC):
    """Nominal owner of one runtime measurement feature vocabulary."""

    @classmethod
    @abstractmethod
    def owns_measurement_feature_name(cls, feature_name: str) -> bool:
        """Return whether this owner emits the canonical or accepted feature name."""

    @classmethod
    @abstractmethod
    def owns_primary_measurement_feature_name(cls, feature_name: str) -> bool:
        """Return whether this owner canonically emits the raw feature name."""


class RuntimeMeasurementFeatureSemanticMarker(ABC):
    """Nominal marker carried by a runtime measurement feature member."""

    family_qualifier: ClassVar[str | None] = None

    @classmethod
    def matches_feature(cls, feature: "RuntimeMeasurementFeature") -> bool:
        """Return whether ``feature`` carries this semantic marker."""
        return any(
            issubclass(marker_type, cls) for marker_type in feature.semantic_markers
        )

    @classmethod
    def qualified_family(cls, feature: "RuntimeMeasurementFeature") -> str:
        """Return a marker-qualified feature family name."""
        if cls.family_qualifier is None:
            raise ValueError(f"{cls.__name__} does not declare family_qualifier.")
        return normalize_runtime_identifier(f"{cls.family_qualifier}_{feature.value}")

    @classmethod
    def requires_sparse_boundary_object_count_stability(cls) -> bool:
        """Return whether sparse-boundary comparison is gated by object count."""
        return True


class ObjectCountFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for object-count measurement features."""

    family_qualifier = "count"
    measurement_dtype: ClassVar[type[object]] = int


class ObjectGroupInvariantFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for object features invariant under invocation grouping."""


class ObjectReferenceFeatureMarker(ObjectGroupInvariantFeatureMarker):
    """Generic marker for measurements whose values reference object identities."""


class ObjectIdentifierFeatureMarker(ObjectReferenceFeatureMarker):
    """Generic marker for an object's own identifier measurement."""

    family_qualifier = "identifier"


class MeasuredObjectAnchorFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for features proving that an object row was measured."""

    family_qualifier = "object"


class ObjectLocationFeatureMarker(ObjectGroupInvariantFeatureMarker):
    """Generic marker for object-location measurement features."""

    family_qualifier = "location"


class ObjectIntensityFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for object-intensity measurement features."""

    family_qualifier = "intensity"


class ObjectCalculatedFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for calculated object measurement features."""

    family_qualifier = "calculated"

    @classmethod
    def requires_sparse_boundary_object_count_stability(cls) -> bool:
        """Calculated object aggregates may gain or lose missing boundary rows."""
        return False


class ObjectShapeDescriptorFeatureMarker(RuntimeMeasurementFeatureSemanticMarker):
    """Generic marker for object shape-descriptor measurement features."""

    family_qualifier = "shape"


class RuntimeMeasurementFeatureDeclaration(ABC, metaclass=AutoRegisterMeta):
    """Registered parser, renderer, and semantic owner for dynamic feature names."""

    __registry_key__ = "declaration_key"
    __skip_if_no_key__ = True
    declaration_key: ClassVar[str | None] = None
    semantic_marker_types: ClassVar[
        tuple[type[RuntimeMeasurementFeatureSemanticMarker], ...]
    ] = ()

    @classmethod
    def require_registered(
        cls,
        declaration_type: type["RuntimeMeasurementFeatureDeclaration"],
    ) -> type["RuntimeMeasurementFeatureDeclaration"]:
        """Return a declaration registered with the dynamic-feature authority."""
        if not isinstance(declaration_type, type) or not issubclass(
            declaration_type,
            RuntimeMeasurementFeatureDeclaration,
        ):
            raise TypeError(
                "Measurement feature declaration must inherit "
                "RuntimeMeasurementFeatureDeclaration."
            )
        if declaration_type not in cls.__registry__.values():
            raise TypeError(
                f"{declaration_type.__name__} is not registered in {cls.__name__}."
            )
        return declaration_type

    @classmethod
    def matching_declarations(
        cls,
        feature_name: str,
    ) -> tuple[tuple[type["RuntimeMeasurementFeatureDeclaration"], object], ...]:
        """Return registered declarations that parse ``feature_name`` exactly."""
        return tuple(
            (declaration_type, identity)
            for declaration_type in cls.__registry__.values()
            for identity in (declaration_type.from_feature_name(feature_name),)
            if identity is not None
        )

    @classmethod
    def semantic_marker_types_for(
        cls,
        feature_name: str,
    ) -> tuple[type[RuntimeMeasurementFeatureSemanticMarker], ...]:
        """Return semantic markers declared by exact dynamic-name owners."""
        return tuple(
            dict.fromkeys(
                marker_type
                for declaration_type, _identity in cls.matching_declarations(
                    feature_name
                )
                for marker_type in declaration_type.semantic_marker_types
            )
        )

    @classmethod
    def feature_has_semantic_marker(
        cls,
        feature_name: str,
        marker_type: type[RuntimeMeasurementFeatureSemanticMarker],
    ) -> bool:
        """Return whether an exact dynamic-name declaration carries ``marker_type``."""
        if not isinstance(marker_type, type) or not issubclass(
            marker_type,
            RuntimeMeasurementFeatureSemanticMarker,
        ):
            raise TypeError(
                "marker_type must inherit RuntimeMeasurementFeatureSemanticMarker."
            )
        return any(
            issubclass(declared_marker_type, marker_type)
            for declared_marker_type in cls.semantic_marker_types_for(feature_name)
        )

    @classmethod
    def indexed_suffix_token_width_for(
        cls,
        feature_tokens: tuple[str, ...],
    ) -> int | None:
        """Return the unique declared trailing descriptor width, when present."""
        suffix_widths = frozenset(
            suffix_width
            for declaration_type in cls.__registry__.values()
            for suffix_width in (
                declaration_type.indexed_suffix_token_width(feature_tokens),
            )
            if suffix_width is not None
        )
        if not suffix_widths:
            return None
        if len(suffix_widths) != 1:
            raise ValueError(
                "Measurement feature declarations disagree on indexed suffix width "
                f"for {feature_tokens!r}: {tuple(sorted(suffix_widths))!r}."
            )
        return next(iter(suffix_widths))

    @classmethod
    @abstractmethod
    def from_feature_name(
        cls,
        feature_name: str,
    ) -> object | None:
        """Parse ``feature_name`` into this declaration's nominal identity."""

    @classmethod
    @abstractmethod
    def feature_name(
        cls,
        identity: object,
    ) -> str:
        """Render one nominal feature identity."""

    @classmethod
    def indexed_suffix_token_width(
        cls,
        feature_tokens: tuple[str, ...],
    ) -> int | None:
        """Return a trailing descriptor width, or none for non-indexed features."""
        del feature_tokens
        return None


class RuntimeMeasurementIndexedDescriptorDeclaration(
    RuntimeMeasurementFeatureDeclaration,
    ABC,
):
    """Dynamic feature declaration whose identity contains an indexed descriptor."""

    @classmethod
    def is_declaration_type(
        cls,
        declaration_type: type[RuntimeMeasurementFeatureDeclaration],
    ) -> bool:
        """Return whether a dynamic declaration owns an indexed descriptor."""
        return issubclass(declaration_type, cls)

    @classmethod
    def require_registered(
        cls,
        declaration_type: type[RuntimeMeasurementFeatureDeclaration],
    ) -> type["RuntimeMeasurementIndexedDescriptorDeclaration"]:
        """Return a registered indexed-descriptor declaration type."""
        registered = super().require_registered(declaration_type)
        if not cls.is_declaration_type(registered):
            raise TypeError(
                "Indexed descriptor declaration must inherit "
                "RuntimeMeasurementIndexedDescriptorDeclaration."
            )
        return registered

    @classmethod
    def matching_declarations(
        cls,
        feature_name: str,
    ) -> tuple[
        tuple[type["RuntimeMeasurementIndexedDescriptorDeclaration"], object], ...
    ]:
        """Return indexed declarations that parse ``feature_name`` exactly."""
        return tuple(
            (declaration_type, identity)
            for declaration_type, identity in super().matching_declarations(
                feature_name
            )
            if cls.is_declaration_type(declaration_type)
        )

    @classmethod
    @abstractmethod
    def indexed_suffix_token_width(
        cls,
        feature_tokens: tuple[str, ...],
    ) -> int | None:
        """Return trailing token width owned by the descriptor index, if any."""


class RuntimeMeasurementFeature(str, Enum):
    """Base for generated runtime measurement feature enums."""

    def __new__(
        cls,
        value: str,
        relations: Iterable[RuntimeMeasurementFeatureRelation] = (),
        semantic_markers: Iterable[type[RuntimeMeasurementFeatureSemanticMarker]] = (),
        indexed_descriptor_declarations: Iterable[
            type[RuntimeMeasurementIndexedDescriptorDeclaration]
        ] = (),
        measurement_row_field_name: str | None = None,
    ):
        descriptor_declarations = tuple(
            RuntimeMeasurementIndexedDescriptorDeclaration.require_registered(
                declaration_type
            )
            for declaration_type in indexed_descriptor_declarations
        )
        member = str_enum_member_with_payload(
            cls, value, payload_attribute="_relations", payload=tuple(relations)
        )
        member.__dict__["_semantic_markers"] = tuple(semantic_markers)
        member.__dict__["_indexed_descriptor_declarations"] = descriptor_declarations
        member.__dict__["_measurement_row_field_name"] = (
            normalize_runtime_identifier(value)
            if measurement_row_field_name is None
            else str(measurement_row_field_name)
        )
        return member

    feature_name = AliasProperty[str]("value")
    relations = AliasProperty[tuple[RuntimeMeasurementFeatureRelation, ...]](
        "_relations"
    )
    semantic_markers = AliasProperty[
        tuple[type[RuntimeMeasurementFeatureSemanticMarker], ...]
    ]("_semantic_markers")
    _indexed_descriptor_declaration_types = AliasProperty[
        tuple[type[RuntimeMeasurementIndexedDescriptorDeclaration], ...]
    ]("_indexed_descriptor_declarations")
    measurement_row_field_name = AliasProperty[str]("_measurement_row_field_name")

    def feature_family(self) -> str:
        """Return this feature's normalized runtime family."""
        return normalize_runtime_identifier(self.value)

    def relation_declarations(
        self,
    ) -> tuple[RuntimeMeasurementFeatureRelationDeclaration, ...]:
        """Return relation declarations owned by this feature member."""
        return tuple(
            (
                RuntimeMeasurementFeatureRelationDeclaration(self, relation)
                for relation in self.relations
            )
        )

    def indexed_descriptor_declarations(
        self,
    ) -> tuple[type[RuntimeMeasurementIndexedDescriptorDeclaration], ...]:
        """Return parser/render declarations owned by this feature member."""
        return self._indexed_descriptor_declaration_types


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementFeatureRelationDeclaration:
    """One producer-owned relation declared between measurement feature families."""

    source_feature: RuntimeMeasurementFeature
    relation: RuntimeMeasurementFeatureRelation

    def source_family_names(
        self, relation_type: type[RuntimeMeasurementFeatureRelation]
    ) -> tuple[str, ...]:
        """Return source families when this declaration belongs to ``relation_type``."""
        if not isinstance(self.relation, relation_type):
            return ()
        return self.relation.source_family_names(self.source_feature)

    def target_family_name(
        self,
        relation_type: type[RuntimeMeasurementFeatureRelation],
        source_family_name: str,
    ) -> str | None:
        """Return the target family for one source family and relation type."""
        if not isinstance(self.relation, relation_type):
            return None
        return self.relation.target_family_name(
            self.source_feature, source_family_name, type(self.source_feature)
        )


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementFeatureRelationDeclarationCollection:
    """Blind query surface over producer-declared feature relations."""

    declarations: tuple[RuntimeMeasurementFeatureRelationDeclaration, ...]

    def __init__(
        self, declarations: Iterable[RuntimeMeasurementFeatureRelationDeclaration]
    ) -> None:
        normalized = tuple(declarations)
        for declaration in normalized:
            if not isinstance(
                declaration, RuntimeMeasurementFeatureRelationDeclaration
            ):
                raise TypeError(
                    "RuntimeMeasurementFeatureRelationDeclarationCollection requires RuntimeMeasurementFeatureRelationDeclaration values."
                )
        object.__setattr__(self, "declarations", normalized)

    def source_family_names(
        self, relation_type: type[RuntimeMeasurementFeatureRelation]
    ) -> tuple[str, ...]:
        """Return all declared source families for one relation type."""
        return tuple(
            (
                family_name
                for declaration in self.declarations
                for family_name in declaration.source_family_names(relation_type)
            )
        )

    def target_family_name(
        self,
        relation_type: type[RuntimeMeasurementFeatureRelation],
        source_family_name: str,
    ) -> str | None:
        """Return the declared target family for one source family."""
        for declaration in self.declarations:
            target_family = declaration.target_family_name(
                relation_type, source_family_name
            )
            if target_family is not None:
                return target_family
        return None


class MeasurementStatistic(str, Enum):
    """Canonical runtime measurement statistic labels."""

    VALUE = "value"
    COUNT = "count"
    MEAN = "mean"


LOCATION_SPATIAL_DOMAIN = VolumeSourceSpatialDomain
"""The spatial domain object locations are reported in (its axis names)."""


ObjectCoreMeasurementFeature = RuntimeMeasurementFeature(
    "ObjectCoreMeasurementFeature",
    {
        "OBJECT_COUNT": "object_count",
        "OBJECT_NUMBER": "object_number",
        **{
            f"CENTER_{axis_name.upper()}": f"center_{axis_name}"
            for axis_name in reversed(LOCATION_SPATIAL_DOMAIN.axis_names)
        },
    },
    module=__name__,
    qualname="ObjectCoreMeasurementFeature",
)
ObjectCoreMeasurementFeature.__doc__ = (
    "Core object-measurement features; one center per location axis."
)


@dataclass(frozen=True, slots=True)
class ObjectLocationCoordinateValues:
    """Dense label-indexed values and missing-row policy for one coordinate."""

    values: Any
    include_missing: bool
    axis_present: bool = True


def object_location_features() -> tuple[ObjectCoreMeasurementFeature, ...]:
    """Return the center features, last array axis first."""
    return tuple(
        ObjectCoreMeasurementFeature(f"center_{axis_name}")
        for axis_name in reversed(LOCATION_SPATIAL_DOMAIN.axis_names)
    )


def object_location_coordinate_arrays(
    axis_centers: Sequence[Any], counts: Any
) -> tuple[tuple[str, ObjectLocationCoordinateValues], ...]:
    """Return one dense label-indexed center per location axis.

    ``axis_centers`` holds one center array per label-array axis. A location
    axis the labels do not have reports zero; for a planar axis an unlabeled
    object's center is missing instead.
    """
    import numpy as np

    coordinates: list[tuple[str, ObjectLocationCoordinateValues]] = []
    for offset, feature in enumerate(object_location_features(), start=1):
        if len(axis_centers) >= offset:
            values = ObjectLocationCoordinateValues(
                axis_centers[-offset], include_missing=False
            )
        else:
            absent = np.zeros(len(counts))
            axis_name = LOCATION_SPATIAL_DOMAIN.axis_names[-offset]
            if axis_name in SourceSpatialDomain.axis_names:
                absent = np.asarray(absent, dtype=float).copy()
                absent[counts == 0] = np.nan
            values = ObjectLocationCoordinateValues(
                absent, include_missing=False, axis_present=False
            )
        coordinates.append((feature.value, values))
    return tuple(coordinates)
@dataclass(frozen=True, slots=True)
class ObjectMeasurementValueRow:
    """Nominal long-form object measurement row."""

    object_label: int
    feature_name: str
    result_value: float


class MeasurementRowAxisField(str, Enum):
    """Canonical row-axis fields for long/tall measurement tables."""

    SLICE_INDEX = "slice_index"
    FEATURE_NAME = "feature_name"
    MEASUREMENT_NAME = "measurement_name"
    OUTPUT_NAME = "output_name"
    OBJECT_NAME = "object_name"
    OBJECT_LABEL = "object_label"
    OBJECT_NUMBER = "object_number"
    OBJECT_ID = "object_id"
    LABEL = "label"
    OBJECT_ROW_IDENTITY = "openhcs_object_row_identity"
    SOURCE_IMAGE_NAME = "source_image_name"
    BIN_INDEX = "bin_index"
    BIN_COUNT = "bin_count"
    SCALE = "scale"
    DIRECTION = "direction"
    GRAY_LEVELS = "gray_levels"
    ZERNIKE_N = "n"
    ZERNIKE_M = "m"

    @classmethod
    def field_names(cls) -> frozenset[str]:
        """Return every canonical row-axis field name."""
        return frozenset(
            (
                *(field.value for field in cls),
                *AxisFamily.active().names(),
            )
        )

    @classmethod
    def object_id_fields(cls) -> tuple["MeasurementRowAxisField", ...]:
        """Return axis fields that can identify an object row."""
        return (
            cls.OBJECT_LABEL,
            cls.OBJECT_NUMBER,
            cls.OBJECT_ID,
            cls.LABEL,
        )

    @classmethod
    def object_id_field_names(cls) -> tuple[str, ...]:
        """Return canonical object-row identity field names."""
        return tuple(field.value for field in cls.object_id_fields())

    @classmethod
    def normalized_object_id_field_names(cls) -> frozenset[str]:
        """Return normalized object-row identity field names."""
        return frozenset(
            normalize_runtime_identifier(field_name)
            for field_name in (
                *cls.object_id_field_names(),
                cls.OBJECT_ROW_IDENTITY.value,
            )
        )

    @classmethod
    def object_ownership_fields(cls) -> tuple["MeasurementRowAxisField", ...]:
        """Return row-axis fields that declare row ownership."""
        return (cls.OBJECT_NAME, cls.SOURCE_IMAGE_NAME)

    @classmethod
    def object_ownership_field_names(cls) -> tuple[str, ...]:
        """Return canonical row ownership field names."""
        return tuple(field.value for field in cls.object_ownership_fields())

    @classmethod
    def feature_name_fields(cls) -> tuple["MeasurementRowAxisField", ...]:
        """Return axis fields that name long-form measurement features."""
        return (cls.FEATURE_NAME, cls.MEASUREMENT_NAME, cls.OUTPUT_NAME)

    @classmethod
    def feature_name_field_names_ordered(cls) -> tuple[str, ...]:
        """Return long-form feature-name fields in semantic priority order."""
        return tuple(field.value for field in cls.feature_name_fields())

    @classmethod
    def feature_name_field_names(cls) -> frozenset[str]:
        """Return canonical long-form feature-name field names."""
        return frozenset(cls.feature_name_field_names_ordered())

    @classmethod
    def normalized_feature_name_field_names(cls) -> frozenset[str]:
        """Return normalized long-form feature-name field names."""
        return frozenset(
            normalize_runtime_identifier(field_name)
            for field_name in cls.feature_name_field_names()
        )


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementRowIdentityContract:
    """Declare row identity precedence, sample numbering and the object-ID field.

    A dialect owns one contract: which fields identify a sample row (primary
    fields win over fallbacks), which field carries the sample number, and
    which fields identify an object.
    """

    primary_sample_fields: frozenset[str] = frozenset({"slice_index"})
    fallback_sample_fields: frozenset[str] = frozenset()
    sample_number_field: str = "sample_number"
    object_identity_fields: tuple[str, ...] = (
        MeasurementRowAxisField.object_id_field_names()
    )
    object_identity_output_field: str = MeasurementRowAxisField.OBJECT_LABEL.value

    def __post_init__(self) -> None:
        primary_sample_fields = frozenset(
            normalize_runtime_identifier(field_name)
            for field_name in self.primary_sample_fields
            if str(field_name).strip()
        )
        fallback_sample_fields = frozenset(
            normalize_runtime_identifier(field_name)
            for field_name in self.fallback_sample_fields
            if str(field_name).strip()
        )
        object_identity_fields = tuple(
            dict.fromkeys(
                normalize_runtime_identifier(field_name)
                for field_name in self.object_identity_fields
                if str(field_name).strip()
            )
        )
        overlap = primary_sample_fields & fallback_sample_fields
        if overlap:
            raise ValueError(
                "RuntimeMeasurementRowIdentityContract fields must be disjoint: "
                f"{sorted(overlap)!r}."
            )
        if not object_identity_fields:
            raise ValueError(
                "RuntimeMeasurementRowIdentityContract.object_identity_fields "
                "cannot be empty."
            )
        output_field = normalize_runtime_identifier(self.object_identity_output_field)
        if not output_field:
            raise ValueError("Object identity output field must be non-empty.")
        sample_number_field = normalize_runtime_identifier(self.sample_number_field)
        if not sample_number_field:
            raise ValueError("Sample number field must be non-empty.")
        object.__setattr__(self, "object_identity_output_field", output_field)
        object.__setattr__(self, "primary_sample_fields", primary_sample_fields)
        object.__setattr__(self, "fallback_sample_fields", fallback_sample_fields)
        object.__setattr__(self, "sample_number_field", sample_number_field)
        object.__setattr__(self, "object_identity_fields", object_identity_fields)

    @property
    def sample_identity_fields(self) -> frozenset[str]:
        """Return every field that can identify a sample row."""
        return self.primary_sample_fields | self.fallback_sample_fields

    def selected_sample_identity_fields(
        self,
        normalized_present_fields: frozenset[str],
    ) -> frozenset[str]:
        """Return the identity fields that own a row under this contract."""
        primary_fields = normalized_present_fields & self.primary_sample_fields
        if primary_fields:
            return primary_fields
        return normalized_present_fields & self.fallback_sample_fields

    def selected_object_identity_field(
        self,
        normalized_present_fields: frozenset[str],
    ) -> str | None:
        """Return the first declared object-identity field present in a row."""
        return next(
            (
                field_name
                for field_name in self.object_identity_fields
                if field_name in normalized_present_fields
            ),
            None,
        )

    def is_sample_number_reference(self, field_name: str) -> bool:
        """Return whether a measurement field refers to another sample's number."""
        return _is_sample_number_reference(self, field_name)

    def is_aggregate_sample_number_reference(self, field_name: str) -> bool:
        """Return whether a measurement field averages sample-number references."""
        return _is_aggregate_sample_number_reference(self, field_name)


@lru_cache(maxsize=32768)
def _is_sample_number_reference(
    contract: RuntimeMeasurementRowIdentityContract,
    field_name: str,
) -> bool:
    normalized = normalize_runtime_identifier(field_name)
    if normalized in contract.sample_identity_fields:
        return False
    parts = tuple(part for part in normalized.split("_") if part)
    number_parts = tuple(contract.sample_number_field.split("_"))
    width = len(number_parts)
    return any(
        parts[index : index + width] == number_parts
        for index in range(len(parts) - width + 1)
    )


@lru_cache(maxsize=32768)
def _is_aggregate_sample_number_reference(
    contract: RuntimeMeasurementRowIdentityContract,
    field_name: str,
) -> bool:
    parts = tuple(
        part for part in normalize_runtime_identifier(field_name).split("_") if part
    )
    return (
        bool(parts)
        and parts[0] == MeasurementStatistic.MEAN.value
        and _is_sample_number_reference(contract, field_name)
    )


class MeasurementRowValueField(str, Enum):
    """Canonical scalar value fields for long/tall measurement rows."""

    RESULT_VALUE = "result_value"
    MEASUREMENT_VALUE = "measurement_value"
    VALUE = "value"
    MEAN_VALUE = "mean_value"

    @classmethod
    def fields(cls) -> tuple["MeasurementRowValueField", ...]:
        """Return scalar measurement value fields in semantic priority order."""
        return (cls.RESULT_VALUE, cls.MEASUREMENT_VALUE, cls.VALUE, cls.MEAN_VALUE)

    @classmethod
    def field_names_ordered(cls) -> tuple[str, ...]:
        """Return scalar measurement value field names in semantic priority order."""
        return tuple(field.value for field in cls.fields())

    @classmethod
    def field_names(cls) -> frozenset[str]:
        """Return every canonical scalar measurement value field name."""
        return frozenset(cls.field_names_ordered())

    @classmethod
    def normalized_field_names(cls) -> frozenset[str]:
        """Return normalized scalar measurement value field names."""
        return frozenset(
            normalize_runtime_identifier(field_name) for field_name in cls.field_names()
        )


@dataclass(frozen=True, slots=True)
class MeasurementScalarLiteral:
    """Scalar classification shared by measurement row and setting policies."""

    raw_value: object
    _NUMERIC_LITERAL_RE: ClassVar[re.Pattern[str]] = re.compile(
        "^[+-]?(?:(?:\\d+(?:\\.\\d*)?|\\.\\d+)(?:[eE][+-]?\\d+)?|nan|inf|infinity)$",
        re.IGNORECASE,
    )

    @property
    def token(self) -> str | None:
        if self.raw_value in (None, ""):
            return None
        if isinstance(self.raw_value, bool):
            return str(int(self.raw_value))
        if isinstance(self.raw_value, (int, float, np.integer, np.floating)):
            return str(self.raw_value)
        if isinstance(self.raw_value, str):
            stripped = self.raw_value.strip()
            return stripped or None
        return None

    @classmethod
    def non_absent_values(cls, values: Sequence[object]) -> np.ndarray:
        """Classify physical cells while retaining explicit nonfinite values."""
        if isinstance(values, np.ndarray) and values.dtype.kind in "iuf":
            return np.ones(values.shape, dtype=bool)
        array = np.asarray(values, dtype=object)
        return np.asarray([not cls(value).is_absent for value in array], dtype=bool)

    @property
    def is_absent(self) -> bool:
        return self.token is None

    @property
    def is_numeric(self) -> bool:
        token = self.token
        return token is not None and self._NUMERIC_LITERAL_RE.match(token) is not None

    @property
    def numeric_value(self) -> float | None:
        token = self.token
        if token is None or self._NUMERIC_LITERAL_RE.match(token) is None:
            return None
        return float(token)

    @property
    def is_finite_numeric(self) -> bool:
        value = self.numeric_value
        return value is not None and math.isfinite(value)

    @property
    def is_nonfinite_numeric(self) -> bool:
        value = self.numeric_value
        return value is not None and (not math.isfinite(value))

    @property
    def finite_numeric_value(self) -> float | None:
        value = self.numeric_value
        return value if value is not None and math.isfinite(value) else None

    @property
    def integer_value(self) -> int | None:
        value = self.finite_numeric_value
        if value is None:
            return None
        integer = int(value)
        return integer if float(integer) == value else None

    @property
    def is_present_axis_value(self) -> bool:
        if self.is_absent:
            return False
        return self.is_finite_numeric if self.is_numeric else True

    @property
    def is_present_measurement_value(self) -> bool:
        if self.is_absent:
            return False
        value = self.numeric_value
        if value is None:
            return True
        return not math.isnan(value)

    @property
    def is_padding_measurement_value(self) -> bool:
        return not self.is_present_measurement_value


def measurement_axis_integer_value(
    value: object, axis: MeasurementRowAxisField
) -> int | None:
    """Return one present integer axis value, or ``None`` for absent values."""
    if value is None:
        return None
    if isinstance(value, str):
        stripped = value.strip()
        if not stripped:
            return None
        literal = MeasurementScalarLiteral(stripped)
        if not literal.is_present_axis_value:
            return None
        integer_value = literal.integer_value
        if integer_value is None:
            raise ValueError(
                f"Measurement axis field {axis.value!r} requires integer-compatible values, got {value!r}."
            )
        return integer_value
    if isinstance(value, (bool, np.bool_)):
        return int(value)
    if isinstance(value, (int, np.integer)):
        return int(value)
    if isinstance(value, (float, np.floating)):
        if not math.isfinite(float(value)):
            return None
        integer = int(value)
        if float(integer) == float(value):
            return integer
        raise ValueError(
            f"Measurement axis field {axis.value!r} requires integer-compatible values, got {value!r}."
        )
    literal = MeasurementScalarLiteral(value)
    if not literal.is_present_axis_value:
        return None
    integer_value = literal.integer_value
    if integer_value is None:
        raise ValueError(
            f"Measurement axis field {axis.value!r} requires integer-compatible values, got {value!r}."
        )
    return integer_value


def measurement_axis_integer_domain(
    values: Sequence[object], axis: MeasurementRowAxisField
) -> tuple[int, ...]:
    """Return the present integer domain for one row-axis value vector."""
    if isinstance(values, np.ndarray) and values.size == 0:
        return ()
    if isinstance(values, np.ndarray) and np.issubdtype(values.dtype, np.bool_):
        return tuple((int(value) for value in np.unique(values)))
    if isinstance(values, np.ndarray) and np.issubdtype(values.dtype, np.integer):
        return tuple((int(value) for value in np.unique(values)))
    if isinstance(values, np.ndarray) and np.issubdtype(values.dtype, np.floating):
        finite_values = values[np.isfinite(values)]
        if finite_values.size == 0:
            return ()
        integer_values = finite_values.astype(np.int64)
        if not bool(np.all(finite_values == integer_values)):
            invalid_value = finite_values[finite_values != integer_values][0]
            raise ValueError(
                f"Measurement axis field {axis.value!r} requires integer-compatible values, got {invalid_value!r}."
            )
        return tuple((int(value) for value in np.unique(integer_values)))
    return tuple(
        dict.fromkeys(
            (
                integer_value
                for value in values
                for integer_value in (measurement_axis_integer_value(value, axis),)
                if integer_value is not None
            )
        )
    )


@dataclass(frozen=True, slots=True)
class ObjectFeatureValueTable:
    """Wide object-feature values aligned onto a declared object-id domain.

    A 1-D feature array holds one value per measured object, in the order of
    ``measured_object_ids``. Each value lands on the row of the object it was
    measured for; a declared object without a measured value gets
    :meth:`missing_value`.
    """

    feature_values: Mapping[str, Any]
    measured_object_ids: tuple[int, ...]
    object_domain: tuple[int, ...]
    object_id_field: str = MeasurementRowAxisField.OBJECT_LABEL.value
    slice_index_field: str = MeasurementRowAxisField.SLICE_INDEX.value
    slice_index: int = 0

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "measured_object_ids",
            ObjectLabelDomain._normalize_ids(
                self.measured_object_ids, "ObjectFeatureValueTable.measured_object_ids"
            ),
        )
        object.__setattr__(
            self,
            "object_domain",
            ObjectLabelDomain._normalize_ids(
                self.object_domain, "ObjectFeatureValueTable.object_domain"
            ),
        )
        object.__setattr__(self, "slice_index", int(self.slice_index))

    @classmethod
    def from_feature_arrays(
        cls,
        feature_values: Mapping[str, Any],
        measured_object_ids: Iterable[int],
        object_domain: Iterable[int],
        **kwargs: Any,
    ) -> "ObjectFeatureValueTable":
        """Build a declared-domain table from measured feature arrays."""
        return cls(
            feature_values=feature_values,
            measured_object_ids=tuple(
                (int(object_id) for object_id in measured_object_ids)
            ),
            object_domain=tuple((int(object_id) for object_id in object_domain)),
            **kwargs,
        )

    def rows(self) -> list[dict[str, float | int]]:
        """Return wide rows ordered by the declared object domain."""
        value_indexes = {
            object_id: index for index, object_id in enumerate(self.measured_object_ids)
        }
        feature_items = []
        for feature_name, values in self.feature_values.items():
            array = np.asarray(values)
            self.validate_feature_values(feature_name, array)
            feature_items.append((feature_name, array.ndim, array.tolist()))
        rows: list[dict[str, float | int]] = []
        for object_id in self.object_domain:
            value_index = value_indexes.get(object_id)
            row: dict[str, float | int] = {
                self.slice_index_field: self.slice_index,
                self.object_id_field: object_id,
            }
            for feature_name, ndim, python_values in feature_items:
                if ndim == 0:
                    row[feature_name] = python_values
                elif value_index is None:
                    row[feature_name] = self.missing_value(feature_name, object_id)
                else:
                    row[feature_name] = python_values[value_index]
            self.complete_row(row)
            rows.append(row)
        return rows

    def validate_feature_values(self, feature_name: str, values: np.ndarray) -> None:
        """Fail when a feature array is not one value per measured object."""
        if values.ndim == 0 or values.shape[0] == len(self.measured_object_ids):
            return
        raise ValueError(
            f"{type(self).__name__} feature {feature_name!r} has {values.shape[0]} "
            f"values for {len(self.measured_object_ids)} measured objects; feature "
            "arrays hold one value per measured object id."
        )

    def missing_value(self, feature_name: str, object_id: int) -> float:
        """Return the value of a declared object that has no measured value."""
        del feature_name, object_id
        return math.nan

    def complete_row(self, row: dict[str, float | int]) -> None:
        """Add table-specific axis/value fields after feature projection."""
        del row


@dataclass(frozen=True, slots=True)
class MeasurementSubject:
    """Entity measured by a measurement table."""

    scope: MeasurementScope
    name: str | None = None
    id_field: str | None = None

    def __post_init__(self) -> None:
        scope = MeasurementScope(
            self.scope,
        )
        object.__setattr__(self, "scope", scope)
        if self.name == "":
            raise ValueError("MeasurementSubject.name cannot be empty.")
        if self.id_field == "":
            raise ValueError("MeasurementSubject.id_field cannot be empty.")
        if scope.requires_subject_name and self.name is None:
            raise ValueError(
                f"MeasurementSubject.name is required for {scope.value} scope."
            )

    @property
    def source_image_name(self) -> str | None:
        """Return the concrete source image represented by this subject, if any."""
        if self.scope is not MeasurementScope.SAMPLE or self.name is None:
            return None
        from openhcs.core.measurement_dialect import MeasurementDialect

        if normalize_runtime_identifier(self.name) in (
            MeasurementDialect.unqualified_sample_names()
        ):
            return None
        return self.name

    @property
    def row_identity_domain(self) -> tuple[MeasurementScope, str | None, str | None]:
        """Return the row domain independently of an image's source qualifier.

        Named image subjects share image-set row identity. Object and relationship
        names identify different row domains and cannot be combined implicitly.
        """

        name = None if self.scope is MeasurementScope.SAMPLE else self.name
        return self.scope, name, self.id_field

    @property
    def object_name(self) -> str | None:
        """Return the concrete object set represented by this subject, if any."""
        return self.name if self.scope is MeasurementScope.OBJECT else None

    @property
    def object_id_field(self) -> str | None:
        """Return the object identifier field represented by this subject."""
        return self.id_field if self.scope is MeasurementScope.OBJECT else None

    @property
    def identity_token(self) -> str:
        """Return the stable identity of this measurement subject."""
        return ":".join(
            (
                "measurement_subject",
                self.scope.value,
                self.name or "",
                self.id_field or "",
            )
        )


@dataclass(frozen=True, slots=True)
class RuntimeScopedMeasurementTable:
    """Measurement table plus the execution scope and record it came from."""

    table: MeasurementTable
    record_identity: str | None = None
    execution_scope: RuntimeExecutionAxisScope | None = None
    occurrence_identity: object = field(
        default_factory=object,
        repr=False,
        compare=False,
    )
