"""How measurement rows are named and shaped.

A :class:`MeasurementDialect` answers every naming question the kernel asks
about measurement rows: which fields identify a sample or an object, how a
scope is spelled, which feature-name prefixes and aliases exist, how row
qualifiers render into feature suffixes, and how lookups resolve external
feature names. :class:`PlainMeasurementDialect` is the kernel's own spelling.
A domain declares its dialect by subclassing and naming its axis family; an
interop format (CellProfiler) declares its dialect in its own package.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
from enum import Enum
from functools import lru_cache, partial
from types import MappingProxyType
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta
from metaclass_registry.caches import ProcessLocalBoundedCache
from metaclass_registry.strategies import EnumKeyedStrategyMixin
from python_introspect import declared_public_names

from openhcs.core.axes import AxisFamily
from openhcs.core.runtime_identifier import (
    normalize_runtime_identifier,
    normalize_runtime_source_name,
    runtime_source_name_tokens,
)
from openhcs.core.runtime_measurements import (
    MeasurementScope,
    RuntimeMeasurementFeatureRelation,
    RuntimeMeasurementFeatureRelationDeclaration,
    RuntimeMeasurementFeatureRelationDeclarationCollection,
    RuntimeMeasurementFeatureSemanticMarker,
    RuntimeMeasurementRowIdentityContract,
)

FeatureParts = tuple[str, ...]


class RuntimeMeasurementSourceNameEncoding(str, Enum):
    """How a dialect encodes source-image identity in measurement features."""

    SEPARATE_KEY = "separate_key"
    FEATURE_SUFFIX = "feature_suffix"


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementSourceQualifiedFeature:
    """Feature identity after applying a dialect's source-name encoding."""

    feature_name: str
    source_name: str | None = None

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "feature_name",
            normalize_runtime_identifier(self.feature_name),
        )
        object.__setattr__(
            self,
            "source_name",
            normalize_runtime_source_name(self.source_name),
        )




class RuntimeMeasurementQualifierValueMode(str, Enum):
    """How a row qualifier value is rendered into a feature suffix."""

    IDENTIFIER = "identifier"
    TWO_DIGIT_INTEGER = "two_digit_integer"
    FRACTION_OF_COUNT = "fraction_of_count"




@dataclass(frozen=True, slots=True)
class RuntimeMeasurementRowQualifier:
    """Declarative row fields that qualify measurement feature names."""

    field_names: tuple[str, ...]
    value_mode: RuntimeMeasurementQualifierValueMode = (
        RuntimeMeasurementQualifierValueMode.IDENTIFIER
    )
    feature_prefixes: tuple[tuple[str, ...], ...] = ()

    def __post_init__(self) -> None:
        field_names = tuple(
            normalize_runtime_identifier(field_name)
            for field_name in self.field_names
            if str(field_name).strip()
        )
        if not field_names:
            raise ValueError(
                "RuntimeMeasurementRowQualifier.field_names cannot be empty."
            )
        object.__setattr__(self, "field_names", field_names)
        object.__setattr__(
            self,
            "value_mode",
            (
                self.value_mode
                if isinstance(
                    self.value_mode,
                    RuntimeMeasurementQualifierValueMode,
                )
                else RuntimeMeasurementQualifierValueMode(self.value_mode)
            ),
        )
        object.__setattr__(
            self,
            "feature_prefixes",
            tuple(
                tuple(
                    normalize_runtime_identifier(part)
                    for part in prefix
                    if str(part).strip()
                )
                for prefix in self.feature_prefixes
            ),
        )


class RuntimeMeasurementQualifierSuffixMatchStrategy(
    EnumKeyedStrategyMixin[RuntimeMeasurementQualifierValueMode],
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Registered suffix parser for one row-qualifier value semantics."""

    __registry_key__ = "strategy_label"
    __skip_if_no_key__ = True
    __enum_member_attr__ = "value_mode"

    value_mode: ClassVar[RuntimeMeasurementQualifierValueMode | None] = None
    strategy_label: ClassVar[str | None] = None

    @abstractmethod
    def matched_token_width(
        self,
        feature_tokens: tuple[str, ...],
        end_index: int,
        qualifier: RuntimeMeasurementRowQualifier,
    ) -> int | None:
        """Return token width owned by ``qualifier`` before ``end_index``."""


class IdentifierQualifierSuffixMatchStrategy(
    RuntimeMeasurementQualifierSuffixMatchStrategy
):
    """Match free-form identifier qualifier suffixes."""

    value_mode = RuntimeMeasurementQualifierValueMode.IDENTIFIER

    def matched_token_width(
        self,
        feature_tokens: tuple[str, ...],
        end_index: int,
        qualifier: RuntimeMeasurementRowQualifier,
    ) -> int | None:
        del feature_tokens, qualifier
        return 1 if end_index > 0 else None


class TwoDigitIntegerQualifierSuffixMatchStrategy(
    RuntimeMeasurementQualifierSuffixMatchStrategy
):
    """Match two-digit integer qualifier suffixes."""

    value_mode = RuntimeMeasurementQualifierValueMode.TWO_DIGIT_INTEGER

    def matched_token_width(
        self,
        feature_tokens: tuple[str, ...],
        end_index: int,
        qualifier: RuntimeMeasurementRowQualifier,
    ) -> int | None:
        del qualifier
        if end_index <= 0:
            return None
        token = feature_tokens[end_index - 1]
        return 1 if len(token) == 2 and token.isdigit() else None


class FractionOfCountQualifierSuffixMatchStrategy(
    RuntimeMeasurementQualifierSuffixMatchStrategy
):
    """Match ``N of M`` fraction-count qualifier suffixes."""

    value_mode = RuntimeMeasurementQualifierValueMode.FRACTION_OF_COUNT

    def matched_token_width(
        self,
        feature_tokens: tuple[str, ...],
        end_index: int,
        qualifier: RuntimeMeasurementRowQualifier,
    ) -> int | None:
        del qualifier
        if end_index < 3:
            return None
        left, of_token, right = feature_tokens[end_index - 3 : end_index]
        return 3 if left.isdigit() and of_token == "of" and right.isdigit() else None


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementRowQualifierSequence:
    """Declared row-qualifier sequence rendered as one feature suffix."""

    field_names_by_qualifier: tuple[tuple[str, ...], ...]

    def __post_init__(self) -> None:
        field_names_by_qualifier = tuple(
            tuple(
                normalize_runtime_identifier(field_name)
                for field_name in field_names
                if str(field_name).strip()
            )
            for field_names in self.field_names_by_qualifier
        )
        if not field_names_by_qualifier or any(
            not field_names for field_names in field_names_by_qualifier
        ):
            raise ValueError(
                "RuntimeMeasurementRowQualifierSequence requires non-empty "
                "qualifier field names."
            )
        object.__setattr__(
            self,
            "field_names_by_qualifier",
            field_names_by_qualifier,
        )


_DEFAULT_MEASUREMENT_ROW_QUALIFIERS = (
    RuntimeMeasurementRowQualifier(("scale",)),
    RuntimeMeasurementRowQualifier(
        ("direction",),
        RuntimeMeasurementQualifierValueMode.TWO_DIGIT_INTEGER,
    ),
    RuntimeMeasurementRowQualifier(("gray_levels",)),
    RuntimeMeasurementRowQualifier(
        ("bin_index", "bin_count"),
        RuntimeMeasurementQualifierValueMode.FRACTION_OF_COUNT,
    ),
)
_DEFAULT_MEASUREMENT_ROW_QUALIFIER_SEQUENCES = (
    RuntimeMeasurementRowQualifierSequence(
        (("scale",), ("direction",), ("gray_levels",))
    ),
    RuntimeMeasurementRowQualifierSequence((("bin_index", "bin_count"),)),
)



def _parts(prefix: Iterable[str]) -> FeatureParts:
    return tuple(part for part in prefix if part)


def _unique_parts(prefixes: Iterable[Iterable[str]]) -> tuple[FeatureParts, ...]:
    return tuple(dict.fromkeys(_parts(prefix) for prefix in prefixes))


def _normalized_feature_families(
    families: Iterable[Iterable[str]],
) -> tuple[FeatureParts, ...]:
    return tuple(
        dict.fromkeys(
            tuple(
                part
                for part in normalize_runtime_identifier("_".join(family)).split("_")
                if part
            )
            for family in families
            if tuple(family)
        )
    )


class MeasurementDialect(ABC, metaclass=AutoRegisterMeta):
    """How measurement rows are named and shaped for one vocabulary.

    Subclasses override the ``*_declarations`` methods and class attributes;
    the public methods normalize and cache what the declarations return. A
    dialect that names an ``axis_family`` is that domain's dialect: the kernel
    names the rows it writes for that family through it. Every named dialect
    registers by ``dialect_name``.
    """

    __registry_key__ = "dialect_name"
    __skip_if_no_key__ = True

    dialect_name: ClassVar[str | None] = None
    axis_family: ClassVar[type[AxisFamily] | None] = None
    row_identity_contract: ClassVar[RuntimeMeasurementRowIdentityContract] = (
        RuntimeMeasurementRowIdentityContract()
    )
    row_qualifiers: ClassVar[tuple[RuntimeMeasurementRowQualifier, ...]] = (
        _DEFAULT_MEASUREMENT_ROW_QUALIFIERS
    )
    source_suffix_qualifier_sequences: ClassVar[
        tuple[RuntimeMeasurementRowQualifierSequence, ...]
    ] = _DEFAULT_MEASUREMENT_ROW_QUALIFIER_SEQUENCES
    threshold_qualifier_tokens: ClassVar[frozenset[str]] = frozenset()
    source_qualifier_prefix_tokens: ClassVar[frozenset[str]] = frozenset()
    source_qualifier_suffix_tokens: ClassVar[frozenset[str]] = frozenset()

    _declaration_generation: ClassVar[int] = 0
    _shared_instances: ClassVar[dict[type["MeasurementDialect"], "MeasurementDialect"]] = {}

    def __init__(self) -> None:
        self._cached_values: dict[str, object] = {}
        self._cached_generation = MeasurementDialect._declaration_generation

    # -- selection ------------------------------------------------------------

    @classmethod
    def shared(cls) -> "MeasurementDialect":
        """Return this dialect's process-wide instance."""
        dialect = MeasurementDialect._shared_instances.get(cls)
        if dialect is None:
            dialect = cls()
            MeasurementDialect._shared_instances[cls] = dialect
        return dialect

    @classmethod
    def for_family(cls, family: type[AxisFamily]) -> "MeasurementDialect":
        """Return the dialect declared for a family, or the kernel's plain dialect."""
        declared = tuple(
            dialect_type
            for dialect_type in MeasurementDialect.__registry__.values()
            if dialect_type.axis_family is family
        )
        if len(declared) > 1:
            raise TypeError(
                f"Axis family {family.__qualname__} has several measurement "
                f"dialects: {[dialect.__qualname__ for dialect in declared]}."
            )
        return (declared[0] if declared else PlainMeasurementDialect).shared()

    @classmethod
    def registered_dialects(cls) -> tuple["MeasurementDialect", ...]:
        """The shared instance of every named dialect."""
        return tuple(
            dialect_type.shared()
            for dialect_type in MeasurementDialect.__registry__.values()
        )

    @classmethod
    def unqualified_sample_names(cls) -> frozenset[str]:
        """Source names that mean "the sample itself" in any registered dialect."""
        return _unqualified_sample_names(tuple(MeasurementDialect.__registry__.values()))

    @classmethod
    def for_active_family(cls) -> "MeasurementDialect":
        return cls.for_family(AxisFamily.active())

    @staticmethod
    def declarations_changed() -> None:
        """Drop cached declarations after a declaring registry gained members."""
        MeasurementDialect._declaration_generation += 1

    def _cached(self, name: str, compute: Callable[[], object]):
        generation = MeasurementDialect._declaration_generation
        if self._cached_generation != generation:
            self._cached_values.clear()
            self._cached_generation = generation
        try:
            return self._cached_values[name]
        except KeyError:
            value = compute()
            self._cached_values[name] = value
            return value

    # -- declarations (override points) ----------------------------------------

    def category_prefix_declarations(self) -> Iterable[FeatureParts]:
        """Measurement categories stripped before feature lookup."""
        return ()

    def primary_category_prefix_declarations(self) -> Iterable[FeatureParts]:
        """Categories whose features are canonical in their owners' tables."""
        return ()

    def feature_part_alias_declarations(self) -> Mapping[FeatureParts, FeatureParts]:
        """Direct feature-part rewrites."""
        return {}

    def alternative_feature_part_alias_declarations(
        self,
    ) -> Mapping[FeatureParts, tuple[FeatureParts, ...]]:
        """Ordered fallback fields for one feature."""
        return {}

    def source_qualified_feature_family_declarations(self) -> Iterable[FeatureParts]:
        """Feature families whose names end in a source-image name."""
        return ()

    def source_feature_prefix_declarations(self) -> Iterable[FeatureParts]:
        return ()

    def calculated_feature_prefix_declarations(self) -> Iterable[FeatureParts]:
        return ()

    def directional_pair_feature_alias_declarations(
        self,
    ) -> Mapping[str, tuple[str, int]]:
        return {}

    def scale_qualified_feature_prefix_declarations(self) -> Iterable[FeatureParts]:
        return ()

    def pair_correlation_feature_name_declaration(self) -> str | None:
        return None

    def pair_regression_slope_feature_name_declaration(self) -> str | None:
        return None

    def undirected_pair_feature_name_declarations(self) -> Iterable[str]:
        return ()

    def threshold_sensitive_pair_feature_name_declarations(self) -> Iterable[str]:
        return ()

    def numbered_feature_prefix_alias_declarations(
        self,
    ) -> Mapping[str, tuple[str, ...]]:
        return {}

    def non_measurement_field_prefix_declarations(self) -> Iterable[str]:
        """Prefixes of structural row fields that are not measurements."""
        return ()

    def feature_relation_declarations(
        self,
    ) -> Iterable[RuntimeMeasurementFeatureRelationDeclaration]:
        return ()

    def measurement_feature_marker_declarations(
        self,
        key: object,
    ) -> Iterable[type[RuntimeMeasurementFeatureSemanticMarker]]:
        del key
        return ()

    def indexed_descriptor_suffix_width(self, feature_parts: FeatureParts) -> int | None:
        """Trailing descriptor-index token width of one feature, if indexed."""
        del feature_parts
        return None

    def source_name_encoding(
        self,
        scope: MeasurementScope,
    ) -> "RuntimeMeasurementSourceNameEncoding":
        """How this dialect encodes source-image identity for a scope."""
        del scope
        return RuntimeMeasurementSourceNameEncoding.SEPARATE_KEY

    def query_object_name(
        self,
        lookup: "RuntimeMeasurementFeatureLookup",
        object_name: str | None,
    ) -> str | None:
        """Row object constraint for one feature lookup."""
        del lookup
        return object_name

    def scope_name(self, scope: MeasurementScope) -> str:
        """Spelling of a measurement scope in this dialect."""
        return scope.value

    def row_field_name(self, field_name: str) -> str:
        """Spelling of one written row field in this dialect."""
        return field_name

    def render_spatial_grid_feature(
        self,
        grid_name: str,
        normalized_grid_name: str,
        normalized_field_name: str,
    ) -> str:
        del grid_name
        return "_".join(("spatial_grid", normalized_grid_name, normalized_field_name))

    def parent_reference_feature_name(self, parent_object_name: str) -> str:
        """Feature naming a child's direct parent object."""
        return f"parent_{parent_object_name}"

    def parent_reference_object_name(self, feature_name: str) -> str | None:
        """Parent object named by a parent-reference feature, if it is one."""
        prefix = self.parent_reference_feature_name("")
        name = feature_name[len(prefix) :] if feature_name.startswith(prefix) else ""
        return name or None

    def child_count_feature_name(self, child_object_name: str) -> str:
        """Feature counting a parent's children of one object set."""
        return f"children_{child_object_name}_count"

    # -- normalized views ------------------------------------------------------

    def row_field_names(self, field_names: Iterable[str]) -> tuple[str, ...]:
        return tuple(self.row_field_name(field_name) for field_name in field_names)

    def category_prefixes(self) -> tuple[FeatureParts, ...]:
        return self._cached(
            "category_prefixes",
            lambda: _unique_parts(self.category_prefix_declarations()),
        )

    def primary_category_prefixes(self) -> tuple[FeatureParts, ...]:
        return self._cached(
            "primary_category_prefixes",
            lambda: _unique_parts(self.primary_category_prefix_declarations()),
        )

    def feature_part_aliases(self) -> Mapping[FeatureParts, FeatureParts]:
        return self._cached(
            "feature_part_aliases",
            lambda: MappingProxyType(
                {
                    _parts(parts): _parts(alias)
                    for parts, alias in self.feature_part_alias_declarations().items()
                }
            ),
        )

    def alternative_feature_part_aliases(
        self,
    ) -> Mapping[FeatureParts, tuple[FeatureParts, ...]]:
        return self._cached(
            "alternative_feature_part_aliases",
            lambda: MappingProxyType(
                {
                    _parts(parts): tuple(
                        _parts(alias) for alias in aliases if tuple(alias)
                    )
                    for parts, aliases in (
                        self.alternative_feature_part_alias_declarations().items()
                    )
                }
            ),
        )

    def source_qualified_feature_families(self) -> tuple[FeatureParts, ...]:
        return self._cached(
            "source_qualified_feature_families",
            lambda: _normalized_feature_families(
                self.source_qualified_feature_family_declarations()
            ),
        )

    def source_feature_prefixes(self) -> tuple[FeatureParts, ...]:
        return self._cached(
            "source_feature_prefixes",
            lambda: _unique_parts(self.source_feature_prefix_declarations()),
        )

    def calculated_feature_prefixes(self) -> tuple[FeatureParts, ...]:
        return self._cached(
            "calculated_feature_prefixes",
            lambda: _unique_parts(self.calculated_feature_prefix_declarations()),
        )

    def scale_qualified_feature_prefixes(self) -> tuple[FeatureParts, ...]:
        return self._cached(
            "scale_qualified_feature_prefixes",
            lambda: _unique_parts(self.scale_qualified_feature_prefix_declarations()),
        )

    def directional_pair_feature_aliases(self) -> Mapping[str, tuple[str, int]]:
        return self._cached(
            "directional_pair_feature_aliases",
            lambda: MappingProxyType(
                {
                    str(name): (str(alias[0]), int(alias[1]))
                    for name, alias in (
                        self.directional_pair_feature_alias_declarations().items()
                    )
                }
            ),
        )

    def numbered_feature_prefix_aliases(self) -> Mapping[str, tuple[str, ...]]:
        return self._cached(
            "numbered_feature_prefix_aliases",
            lambda: MappingProxyType(
                {
                    normalize_runtime_identifier(prefix): tuple(
                        normalize_runtime_identifier(part)
                        for part in alias
                        if str(part).strip()
                    )
                    for prefix, alias in (
                        self.numbered_feature_prefix_alias_declarations().items()
                    )
                    if str(prefix).strip()
                }
            ),
        )

    def pair_correlation_feature_name(self) -> str | None:
        value = self.pair_correlation_feature_name_declaration()
        return None if value is None else normalize_runtime_identifier(value)

    def pair_regression_slope_feature_name(self) -> str | None:
        value = self.pair_regression_slope_feature_name_declaration()
        return None if value is None else normalize_runtime_identifier(value)

    def undirected_pair_feature_names(self) -> frozenset[str]:
        return self._cached(
            "undirected_pair_feature_names",
            lambda: frozenset(
                normalize_runtime_identifier(name)
                for name in self.undirected_pair_feature_name_declarations()
            ),
        )

    def threshold_sensitive_pair_feature_names(self) -> frozenset[str]:
        return self._cached(
            "threshold_sensitive_pair_feature_names",
            lambda: frozenset(
                normalize_runtime_identifier(name)
                for name in self.threshold_sensitive_pair_feature_name_declarations()
            ),
        )

    @property
    def non_measurement_field_prefixes(self) -> tuple[str, ...]:
        """Normalized structural-field prefixes declared by the dialect."""
        return self._cached(
            "non_measurement_field_prefixes",
            lambda: tuple(
                normalize_runtime_identifier(prefix).rstrip("_") + "_"
                for prefix in self.non_measurement_field_prefix_declarations()
                if str(prefix).strip()
            ),
        )

    def measurement_feature_relation_declarations(
        self,
    ) -> RuntimeMeasurementFeatureRelationDeclarationCollection:
        """Producer-declared measurement-feature relations."""
        return RuntimeMeasurementFeatureRelationDeclarationCollection(
            tuple(self.feature_relation_declarations())
        )

    def measurement_feature_marker_types(
        self,
        key: object,
    ) -> tuple[type[RuntimeMeasurementFeatureSemanticMarker], ...]:
        """Producer-declared semantic marker types for one feature key."""
        marker_types = tuple(self.measurement_feature_marker_declarations(key))
        for marker_type in marker_types:
            if not isinstance(marker_type, type) or not issubclass(
                marker_type,
                RuntimeMeasurementFeatureSemanticMarker,
            ):
                raise TypeError(
                    f"{type(self).__name__}.measurement_feature_marker_declarations "
                    "must return RuntimeMeasurementFeatureSemanticMarker types."
                )
        return marker_types

    def feature_name_has_primary_category(self, feature_name: str) -> bool:
        """Return whether a raw feature uses an owner-declared primary category."""
        parts = tuple(
            part
            for part in normalize_runtime_identifier(feature_name).split("_")
            if part
        )
        return any(
            len(parts) > len(prefix) and parts[: len(prefix)] == prefix
            for prefix in self.primary_category_prefixes()
        )

    def spatial_grid_measurement_feature_name(
        self,
        grid_name: str,
        field_name: str,
    ) -> str:
        """Render one canonical spatial-grid field in this dialect."""
        return self.render_spatial_grid_feature(
            grid_name,
            normalize_runtime_identifier(grid_name),
            normalize_runtime_identifier(field_name),
        )

    @property
    def projected_feature_name(
        self,
    ) -> Callable[[str, tuple[tuple[str, object], ...]], str]:
        """Bind this dialect's grammar for one producer admission."""
        return partial(_projected_feature_name, self)

    # -- feature lookup --------------------------------------------------------

    def feature_parts(self, parts: FeatureParts) -> FeatureParts:
        """Return dialect-normalized feature parts for one lookup token."""
        resolved_parts = parts
        for prefix in self.category_prefixes():
            if len(resolved_parts) > len(prefix) and resolved_parts[: len(prefix)] == prefix:
                resolved_parts = resolved_parts[len(prefix) :]
                break
        return self.feature_part_aliases().get(resolved_parts, resolved_parts)

    def alternative_feature_parts(self, parts: FeatureParts) -> tuple[FeatureParts, ...]:
        """Return ordered semantic fallback fields for one lookup token."""
        return self.alternative_feature_part_aliases().get(self.feature_parts(parts), ())

    def feature_lookup(self, feature_name: str) -> "RuntimeMeasurementFeatureLookup":
        """Return the lookup identity for one external feature name."""
        return RuntimeMeasurementFeatureLookup(feature_name, self)

    # -- source-qualified features ---------------------------------------------

    def source_feature_family_for_relation(
        self,
        relation_type: type[RuntimeMeasurementFeatureRelation],
        feature_name: str,
        source_name: str | None,
        scope: MeasurementScope,
    ) -> RuntimeMeasurementSourceQualifiedFeature | None:
        """Return the source-qualified family for one declared relation type."""
        return self.source_qualified_feature_family(
            feature_name,
            source_name,
            scope,
            self.measurement_feature_relation_declarations().source_family_names(
                relation_type,
            ),
        )

    def target_family_for_relation_source_family(
        self,
        relation_type: type[RuntimeMeasurementFeatureRelation],
        source_family_name: str,
    ) -> str | None:
        """Return the declared target family for one relation source family."""
        return self.measurement_feature_relation_declarations().target_family_name(
            relation_type,
            source_family_name,
        )

    def encode_source_qualified_feature(
        self,
        feature_name: str,
        source_name: str | None,
        scope: MeasurementScope,
        *,
        qualifiers: tuple[str, ...] = (),
    ) -> RuntimeMeasurementSourceQualifiedFeature:
        """Encode source identity into a feature according to this dialect."""
        normalized_feature_name = normalize_runtime_identifier(feature_name)
        normalized_source_name = normalize_runtime_source_name(source_name)
        encoding = self.source_name_encoding(scope)
        if (
            normalized_source_name is None
            or encoding is RuntimeMeasurementSourceNameEncoding.SEPARATE_KEY
        ):
            return RuntimeMeasurementSourceQualifiedFeature(
                normalized_feature_name,
                normalized_source_name,
            )
        if encoding is not RuntimeMeasurementSourceNameEncoding.FEATURE_SUFFIX:
            raise ValueError(
                f"Unsupported measurement source-name encoding: {encoding}."
            )
        source_tokens = runtime_source_name_tokens(normalized_source_name)
        if not source_tokens:
            return RuntimeMeasurementSourceQualifiedFeature(normalized_feature_name)
        feature_tokens = tuple(
            token for token in normalized_feature_name.split("_") if token
        )
        qualifier_tokens = self.source_qualified_feature_qualifier_tokens(qualifiers)
        encoded_tokens = self.place_feature_suffix_source_tokens(
            feature_tokens,
            source_tokens,
            qualifier_tokens,
        )
        return RuntimeMeasurementSourceQualifiedFeature("_".join(encoded_tokens))

    def source_qualified_feature_qualifier_tokens(
        self,
        qualifiers: tuple[str, ...],
    ) -> tuple[str, ...]:
        """Return qualifier tokens used to place feature-suffix source names."""
        return tuple(
            token
            for qualifier in qualifiers
            for token in normalize_runtime_identifier(qualifier).split("_")
            if token
        )

    def place_feature_suffix_source_tokens(
        self,
        feature_tokens: tuple[str, ...],
        source_tokens: tuple[str, ...],
        qualifier_tokens: tuple[str, ...] = (),
    ) -> tuple[str, ...]:
        """Place feature-suffix source tokens before declared row qualifiers."""
        if not source_tokens:
            return feature_tokens
        if not qualifier_tokens:
            qualifier_tokens = self.infer_feature_suffix_qualifier_tokens(
                feature_tokens
            )
        suffix_start = self.feature_suffix_source_insertion_index(
            feature_tokens,
            qualifier_tokens,
        )
        if (
            feature_tokens[suffix_start - len(source_tokens) : suffix_start]
            == source_tokens
        ):
            return feature_tokens
        if feature_tokens[-len(source_tokens) :] == source_tokens:
            return feature_tokens
        return (
            *feature_tokens[:suffix_start],
            *source_tokens,
            *feature_tokens[suffix_start:],
        )

    def infer_feature_suffix_qualifier_tokens(
        self,
        feature_tokens: tuple[str, ...],
    ) -> tuple[str, ...]:
        """Infer declared row-qualifier suffix tokens from a flat feature name."""
        descriptor_suffix_width = self.indexed_descriptor_suffix_token_width(
            feature_tokens
        )
        if descriptor_suffix_width is not None:
            return feature_tokens[-descriptor_suffix_width:]
        matches: list[tuple[str, ...]] = []
        for qualifiers in self.source_suffix_qualifier_sequence_qualifiers():
            suffix_length = self.match_feature_suffix_qualifier_sequence(
                feature_tokens,
                qualifiers,
            )
            if suffix_length is None:
                continue
            suffix_tokens = feature_tokens[-suffix_length:]
            if not self.qualifier_sequence_identifies_feature_suffix(
                feature_tokens,
                suffix_tokens,
                qualifiers,
            ):
                continue
            matches.append(suffix_tokens)
        if not matches:
            return ()
        return max(matches, key=len)

    def indexed_descriptor_suffix_token_width(
        self,
        feature_tokens: tuple[str, ...],
    ) -> int | None:
        """Return the trailing descriptor-index token width declared for a feature."""
        suffix_width = self.indexed_descriptor_suffix_width(tuple(feature_tokens))
        if suffix_width is None:
            return None
        suffix_width = int(suffix_width)
        if suffix_width <= 0 or suffix_width > len(feature_tokens):
            raise ValueError(
                "Indexed descriptor suffix width must be within feature token "
                f"bounds: width={suffix_width!r}, tokens={feature_tokens!r}."
            )
        return suffix_width

    def source_suffix_qualifier_sequence_qualifiers(
        self,
    ) -> tuple[tuple[RuntimeMeasurementRowQualifier, ...], ...]:
        """Return declared source-suffix qualifier sequences as qualifier objects."""
        qualifiers_by_fields = {
            qualifier.field_names: qualifier for qualifier in self.row_qualifiers
        }
        sequences: list[tuple[RuntimeMeasurementRowQualifier, ...]] = []
        for sequence in self.source_suffix_qualifier_sequences:
            qualifiers: list[RuntimeMeasurementRowQualifier] = []
            for field_names in sequence.field_names_by_qualifier:
                qualifier = qualifiers_by_fields.get(field_names)
                if qualifier is None:
                    raise ValueError(
                        f"{type(self).__name__} source suffix qualifier "
                        f"sequence references undeclared qualifier {field_names!r}."
                    )
                qualifiers.append(qualifier)
            sequences.append(tuple(qualifiers))
        return tuple(sequences)

    def match_feature_suffix_qualifier_sequence(
        self,
        feature_tokens: tuple[str, ...],
        qualifiers: tuple[RuntimeMeasurementRowQualifier, ...],
    ) -> int | None:
        """Return matched suffix length for a declared qualifier sequence."""
        cursor = len(feature_tokens)
        for qualifier in reversed(qualifiers):
            token_count = (
                RuntimeMeasurementQualifierSuffixMatchStrategy.for_enum_member(
                    qualifier.value_mode
                ).matched_token_width(feature_tokens, cursor, qualifier)
            )
            if token_count is None:
                return None
            cursor -= token_count
        return len(feature_tokens) - cursor

    def qualifier_sequence_identifies_feature_suffix(
        self,
        feature_tokens: tuple[str, ...],
        suffix_tokens: tuple[str, ...],
        qualifiers: tuple[RuntimeMeasurementRowQualifier, ...],
    ) -> bool:
        """Return whether a qualifier sequence is distinctive enough to infer."""
        if any(
            qualifier.value_mode is not RuntimeMeasurementQualifierValueMode.IDENTIFIER
            for qualifier in qualifiers
        ):
            return True
        base_tokens = feature_tokens[: len(feature_tokens) - len(suffix_tokens)]
        return any(
            base_tokens == prefix
            for prefix in self.scale_qualified_feature_prefixes()
        )

    def feature_suffix_source_insertion_index(
        self,
        feature_tokens: tuple[str, ...],
        qualifier_tokens: tuple[str, ...] = (),
    ) -> int:
        """Return where feature-suffix source identity belongs."""
        if (
            qualifier_tokens
            and len(feature_tokens) >= len(qualifier_tokens)
            and feature_tokens[-len(qualifier_tokens) :] == qualifier_tokens
        ):
            return len(feature_tokens) - len(qualifier_tokens)
        return len(feature_tokens)

    def source_qualified_feature_family(
        self,
        feature_name: str,
        source_name: str | None,
        scope: MeasurementScope,
        feature_families: Iterable[str],
    ) -> RuntimeMeasurementSourceQualifiedFeature | None:
        """Bind a feature to a declared base family and source identity."""
        normalized_feature_name = normalize_runtime_identifier(feature_name)
        normalized_source_name = normalize_runtime_source_name(source_name)
        normalized_families = tuple(
            sorted(
                {
                    normalize_runtime_identifier(family)
                    for family in feature_families
                    if str(family).strip()
                },
                key=lambda family: (-len(family), family),
            )
        )
        if not normalized_families:
            return None
        encoding = self.source_name_encoding(scope)
        if encoding is RuntimeMeasurementSourceNameEncoding.SEPARATE_KEY:
            if normalized_feature_name in normalized_families:
                return RuntimeMeasurementSourceQualifiedFeature(
                    normalized_feature_name,
                    normalized_source_name,
                )
            return None
        if encoding is not RuntimeMeasurementSourceNameEncoding.FEATURE_SUFFIX:
            raise ValueError(
                f"Unsupported measurement source-name encoding: {encoding}."
            )
        if normalized_feature_name in normalized_families:
            return RuntimeMeasurementSourceQualifiedFeature(normalized_feature_name)
        for family in normalized_families:
            prefix = f"{family}_"
            if normalized_feature_name.startswith(prefix):
                return RuntimeMeasurementSourceQualifiedFeature(
                    family,
                    normalized_feature_name[len(prefix) :],
                )
        return None



@lru_cache(maxsize=8)
def _unqualified_sample_names(
    dialect_types: tuple[type[MeasurementDialect], ...],
) -> frozenset[str]:
    return frozenset(
        (
            "",
            *(
                normalize_runtime_identifier(
                    dialect_type.shared().scope_name(MeasurementScope.SAMPLE)
                )
                for dialect_type in dialect_types
            ),
        )
    )


class PlainMeasurementDialect(MeasurementDialect):
    """The kernel's own spelling: kernel field names, no external vocabulary."""

    dialect_name = "plain"


@lru_cache(maxsize=8192)
def _projected_feature_name(
    dialect: MeasurementDialect,
    feature_name: str,
    qualifier_values: tuple[tuple[str, object], ...],
) -> str:
    from openhcs.core.equivalence.measurement_rows import measurement_row_qualifiers

    qualifiers = measurement_row_qualifiers(
        dict(qualifier_values),
        dialect,
        feature_name,
    )
    return "_".join((feature_name, *qualifiers)) if qualifiers else feature_name


def _compact_identifier(value: str) -> str:
    return value.replace("_", "")


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementFeatureAliasSpan:
    """One field-name span accepted for measurement lookup."""

    parts: tuple[str, ...]

    @property
    def name(self) -> str:
        return "_".join(self.parts)

    @property
    def field_aliases(self) -> tuple[str, ...]:
        name = self.name
        if not name:
            return ()
        compact = _compact_identifier(name)
        if compact == name:
            return (name,)
        return (name, compact)


class RuntimeMeasurementLookupAliasCache(
    ProcessLocalBoundedCache[tuple[str, int, str], tuple[str, ...]]
):
    """Process-local cache for dialect-resolved measurement lookup aliases."""


@dataclass(frozen=True, slots=True)
class RuntimeMeasurementFeatureLookup:
    """Dialect-resolved aliases for one runtime measurement feature."""

    feature_name: str
    dialect: MeasurementDialect

    @property
    def normalized_name(self) -> str:
        return normalize_runtime_identifier(self.feature_name)

    @property
    def normalized_parts(self) -> tuple[str, ...]:
        return tuple(part for part in self.normalized_name.split("_") if part)

    @property
    def normalized_segments(self) -> tuple[tuple[str, ...], ...]:
        return tuple(
            tuple(
                part
                for part in normalize_runtime_identifier(segment).split("_")
                if part
            )
            for segment in str(self.feature_name).split("_")
            if segment
        )

    @property
    def field_aliases(self) -> tuple[str, ...]:
        """Return schema-safe feature field aliases."""
        cache = RuntimeMeasurementLookupAliasCache.process_cache()
        cache_key = ("field", id(self.dialect), self.feature_name)
        cached = cache.cached_value(cache_key)
        if cached is not None:
            return cached
        aliases: list[str] = []
        for span in self.field_alias_spans:
            for alias in span.field_aliases:
                if alias and alias not in aliases:
                    aliases.append(alias)
        return cache.store_value(cache_key, tuple(aliases))

    @property
    def source_aliases(self) -> tuple[str, ...]:
        """Return source-image aliases encoded by a source-qualified feature."""
        cache = RuntimeMeasurementLookupAliasCache.process_cache()
        cache_key = ("source", id(self.dialect), self.feature_name)
        cached = cache.cached_value(cache_key)
        if cached is not None:
            return cached
        return cache.store_value(
            cache_key,
            self.compact_identifier_aliases(self.source_names),
        )

    @property
    def dialect_feature_name(self) -> str:
        return "_".join(self.dialect.feature_parts(self.normalized_parts))

    @property
    def source_names(self) -> tuple[str, ...]:
        names: list[str] = []
        feature_parts = self.dialect_feature_parts
        suffix_width = self.dialect.indexed_descriptor_suffix_width(
            self.normalized_parts
        )
        source_end = len(feature_parts) - (0 if suffix_width is None else suffix_width)
        for feature_family in self.source_qualified_feature_families:
            source_name = "_".join(feature_parts[len(feature_family) : source_end])
            if source_name and source_name not in names:
                names.append(source_name)
        return tuple(names)

    @property
    def source_qualified_field_names(self) -> tuple[str, ...]:
        return self.compact_identifier_aliases(
            "_".join(feature_family)
            for feature_family in self.source_qualified_feature_families
        )

    def compact_identifier_aliases(self, names: Iterable[str]) -> tuple[str, ...]:
        """Return ordered normalized and compact aliases for non-empty names."""
        aliases: list[str] = []
        for name in names:
            for alias in (name, _compact_identifier(name)):
                if alias and alias not in aliases:
                    aliases.append(alias)
        return tuple(aliases)

    @property
    def source_qualified_feature_families(self) -> tuple[tuple[str, ...], ...]:
        dialect_feature_parts = self.dialect_feature_parts
        families: list[tuple[str, ...]] = []
        for family in self.dialect.source_qualified_feature_families():
            if len(dialect_feature_parts) <= len(family):
                continue
            if dialect_feature_parts[: len(family)] != family:
                continue
            families.append(family)
        return tuple(families)

    @property
    def dialect_feature_parts(self) -> tuple[str, ...]:
        return self.dialect.feature_parts(self.normalized_parts)

    @property
    def alternative_feature_parts(self) -> tuple[tuple[str, ...], ...]:
        return self.dialect.alternative_feature_parts(self.normalized_parts)

    @property
    def field_alias_spans(self) -> tuple[RuntimeMeasurementFeatureAliasSpan, ...]:
        """Return field-name spans from most specific to broadest."""
        spans: list[RuntimeMeasurementFeatureAliasSpan] = []
        for parts in (
            self.normalized_parts,
            self.dialect_feature_parts,
            *self.alternative_feature_parts,
            *self.source_qualified_feature_families,
            self.unqualified_feature_parts,
            self.metric_family_parts,
        ):
            if not parts:
                continue
            span = RuntimeMeasurementFeatureAliasSpan(parts)
            if span not in spans:
                spans.append(span)
        return tuple(spans)

    @property
    def unqualified_feature_parts(self) -> tuple[str, ...]:
        """Return the feature with an external measurement category removed."""
        segments = self.normalized_segments
        if len(segments) < 2:
            return ()
        return tuple(part for segment in segments[1:] for part in segment)

    @property
    def metric_family_parts(self) -> tuple[str, ...]:
        """Return the feature metric without category or terminal qualifier."""
        segments = self.normalized_segments
        if len(segments) < 3:
            return ()
        return segments[1]

    def query_object_name(self, object_name: str | None) -> str | None:
        """Return the effective row object constraint for this feature."""
        return self.dialect.query_object_name(self, object_name)


_EXECUTING_MEASUREMENT_DIALECT: ContextVar[MeasurementDialect | None] = ContextVar(
    "executing_measurement_dialect",
    default=None,
)


class MeasurementDialectReference(ABC):
    """A dialect resolved when a query runs rather than when it is declared."""

    @abstractmethod
    def resolve(self) -> MeasurementDialect:
        """Return the dialect for the running scope."""


@dataclass(frozen=True, slots=True)
class ExecutingMeasurementDialect(MeasurementDialectReference):
    """The dialect of the function executing now, else the active family's."""

    def resolve(self) -> MeasurementDialect:
        dialect = _EXECUTING_MEASUREMENT_DIALECT.get()
        return MeasurementDialect.for_active_family() if dialect is None else dialect


EXECUTING_MEASUREMENT_DIALECT = ExecutingMeasurementDialect()
MeasurementDialectLike = MeasurementDialect | MeasurementDialectReference


def resolve_measurement_dialect(dialect: MeasurementDialectLike) -> MeasurementDialect:
    """Resolve a dialect or a dialect reference."""
    if isinstance(dialect, MeasurementDialect):
        return dialect
    if isinstance(dialect, MeasurementDialectReference):
        return dialect.resolve()
    raise TypeError(
        "Expected MeasurementDialect or MeasurementDialectReference, "
        f"got {type(dialect).__name__}."
    )


@contextmanager
def executing_measurement_dialect(dialect: MeasurementDialect) -> Iterator[None]:
    """Bind the dialect of the function executing in this scope."""
    if not isinstance(dialect, MeasurementDialect):
        raise TypeError(
            "executing_measurement_dialect requires MeasurementDialect, got "
            f"{type(dialect).__name__}."
        )
    token = _EXECUTING_MEASUREMENT_DIALECT.set(dialect)
    try:
        yield
    finally:
        _EXECUTING_MEASUREMENT_DIALECT.reset(token)


__all__ = declared_public_names(
    globals(),
    constant_prefixes=("EXECUTING_MEASUREMENT_DIALECT",),
)
