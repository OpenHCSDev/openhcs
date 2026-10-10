"""Typed source metadata roles shared across source matching and runtime contexts."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum, StrEnum
from functools import lru_cache
from math import isfinite
from pathlib import Path
from types import MappingProxyType
from typing import ClassVar, NoReturn, Self, TYPE_CHECKING, TypeAlias, TypeVar

from metaclass_registry import AutoRegisterMeta
from zmqruntime.viewer_protocol import ViewerWireField

from openhcs.constants.constants import AllComponents
from metaclass_registry.strategies import EnumKeyedStrategyMixin

if TYPE_CHECKING:
    from openhcs.core.source_bindings import MetadataExtractionRule
    from openhcs.microscopes.microscope_interfaces import FilenameParser


ORIGINAL_SOURCE_METADATA_FIELD = "OpenHCSOriginalSourceMetadata"
SOURCE_FILTER_PATHS_METADATA_FIELD = "OpenHCSSourceFilterPaths"
SOURCE_PLANE_INDEX_FIELD = "source_plane_index"
SOURCE_PLANE_COUNT_FIELD = "source_plane_count"
SOURCE_VOXEL_SPACING_FIELD = "OpenHCSSourceVoxelSpacingZYX"
SOURCE_VOXEL_SPACING_UNIT_FIELD = "OpenHCSSourceVoxelSpacingUnit"

SourceMetadataNonNullScalar: TypeAlias = str | int | float | bool
SourceMetadataScalar: TypeAlias = SourceMetadataNonNullScalar | None
SourceMetadataValue: TypeAlias = (
    SourceMetadataScalar | Mapping[str, SourceMetadataScalar]
)
SourceMetadataMapping: TypeAlias = Mapping[str, SourceMetadataValue]
SourceMetadataIdentityValue: TypeAlias = (
    SourceMetadataScalar | tuple[tuple[str, SourceMetadataScalar], ...]
)
SourceMetadataIdentityItems: TypeAlias = tuple[
    tuple[str, SourceMetadataIdentityValue],
    ...,
]


_MetadataViewT = TypeVar("_MetadataViewT")


@dataclass(frozen=True, slots=True, eq=False)
class SourceMetadataFields(Mapping[str, SourceMetadataValue]):
    """Common field projection algorithms with nominal lifetime-selected views."""

    fields: tuple[tuple[str, SourceMetadataValue], ...]

    @staticmethod
    def canonical_component_value(
        component: AllComponents | None,
        value: SourceMetadataScalar,
    ) -> str | int:
        """Canonicalize numeric variable coordinates while retaining labels."""
        if component is None or not component.is_variable_axis():
            return str(value)
        value_text = str(value)
        return int(value_text) if value_text.isdecimal() else value_text

    @classmethod
    def from_mapping(cls, metadata: SourceMetadataMapping) -> Self:
        return cls(tuple(metadata.items()))

    @classmethod
    def normalized_value(cls, value: SourceMetadataValue) -> SourceMetadataValue:
        if isinstance(value, Mapping):
            return MappingProxyType(
                {
                    str(key): cls.normalized_scalar(nested_value)
                    for key, nested_value in value.items()
                }
            )
        return cls.normalized_scalar(value)

    @classmethod
    def normalized_mapping(
        cls, metadata: SourceMetadataMapping
    ) -> SourceMetadataMapping:
        return MappingProxyType(
            {str(key): cls.normalized_value(value) for key, value in metadata.items()}
        )

    @classmethod
    def normalized_scalar(cls, value: SourceMetadataScalar) -> SourceMetadataScalar:
        """Admit the shared scalar grammar before applying the owner's policy."""
        if value is None:
            return None
        if isinstance(value, SourceMetadataNonNullScalar):
            return cls._normalize_admitted_scalar(value)
        return cls._reject_scalar(value)

    @staticmethod
    def _normalize_admitted_scalar(
        value: SourceMetadataNonNullScalar,
    ) -> SourceMetadataNonNullScalar:
        if isinstance(value, str):
            return canonical_path_metadata_value(value)
        return value

    @staticmethod
    def _reject_scalar(value: object) -> NoReturn:
        raise TypeError(
            "Source metadata scalar values must be str, int, float, bool, or None, "
            f"got {type(value).__name__}."
        )

    def __getitem__(self, key: str) -> SourceMetadataValue:
        for field_key, value in self.fields:
            if field_key == key:
                return value
        raise KeyError(key)

    def __iter__(self) -> Iterator[str]:
        return (key for key, _value in self.fields)

    def __len__(self) -> int:
        return len(self.fields)

    @abstractmethod
    def __eq__(self, other: object) -> bool:
        """Compare through the declared record or mapping namespace."""

    def _derived_view(
        self, key: str | AllComponents, derive: Callable[[], _MetadataViewT]
    ) -> _MetadataViewT:
        return derive()

    @staticmethod
    def _view(
        metadata: SourceMetadataMapping,
        key: str | AllComponents,
        derive: Callable[[], _MetadataViewT],
    ) -> _MetadataViewT:
        if isinstance(metadata, SourceMetadataFields):
            return metadata._derived_view(key, derive)
        return derive()

    @classmethod
    def scalar_items(
        cls, metadata: SourceMetadataMapping
    ) -> tuple[tuple[str, SourceMetadataScalar], ...]:
        """Read current raw fields or the immutable owner's scalar projection."""
        return cls._view(
            metadata,
            "scalar_items",
            lambda: tuple(
                (str(key), value)
                for key, value in metadata.items()
                if key != ORIGINAL_SOURCE_METADATA_FIELD
                and not isinstance(value, Mapping)
            ),
        )

    @classmethod
    def scalar_values(
        cls, metadata: SourceMetadataMapping
    ) -> tuple[SourceMetadataScalar, ...]:
        return tuple(value for _key, value in cls.scalar_items(metadata))

    @classmethod
    def original_items(
        cls, metadata: SourceMetadataMapping
    ) -> tuple[tuple[str, SourceMetadataScalar], ...]:
        def project() -> tuple[tuple[str, SourceMetadataScalar], ...]:
            original_metadata = metadata.get(ORIGINAL_SOURCE_METADATA_FIELD)
            if original_metadata is None:
                return ()
            return OriginalSourceMetadata.from_reserved_value(
                original_metadata, path=ORIGINAL_SOURCE_METADATA_FIELD
            ).fields

        return cls._view(metadata, "original_items", project)

    @classmethod
    def source_filter_paths(cls, metadata: SourceMetadataMapping) -> tuple[str, ...]:
        def project() -> tuple[str, ...]:
            paths = metadata.get(SOURCE_FILTER_PATHS_METADATA_FIELD)
            if paths is None:
                return ()
            return SourceFilterPathMetadata.from_reserved_value(
                paths, path=SOURCE_FILTER_PATHS_METADATA_FIELD
            ).paths

        return cls._view(metadata, "source_filter_paths", project)

    @classmethod
    def identity_items(
        cls, metadata: SourceMetadataMapping
    ) -> SourceMetadataIdentityItems:
        def project() -> SourceMetadataIdentityItems:
            return tuple(
                sorted(
                    (
                        str(key),
                        (
                            tuple(sorted((str(k), v) for k, v in value.items()))
                            if isinstance(value, Mapping)
                            else value
                        ),
                    )
                    for key, value in metadata.items()
                )
            )

        return cls._view(metadata, "identity_items", project)

    @classmethod
    def provenance_identity_items(
        cls, metadata: SourceMetadataMapping
    ) -> tuple[tuple[str, str], ...]:
        """Derive stable provenance identity from the owner's canonical field view."""
        return cls._view(
            metadata,
            "provenance_identity_items",
            lambda: tuple((key, repr(value)) for key, value in cls.identity_items(metadata)),
        )

    @staticmethod
    def literal_value(
        metadata: SourceMetadataMapping, key: str
    ) -> SourceMetadataScalar:
        if isinstance(metadata, SourceMetadataFields):
            return metadata._literal_value(key)
        return SourceMetadataFields._literal_value(metadata, key)

    def _literal_value(self, key: str) -> SourceMetadataScalar:
        # Preserve the existing lookup's role-validation order even when the
        # requested literal could be read without the original metadata role.
        scalars = SourceMetadataFields.scalar_items(self)
        original = SourceMetadataFields.original_items(self)
        for fields in (original, scalars):
            for candidate_key, value in fields:
                if str(candidate_key) == key and value is not None:
                    return value
        return None

    @property
    def _admitted_components_complete(self) -> bool:
        """Whether retained, already demanded views cover every component slot."""
        return False

    @classmethod
    def literal_field_types(
        cls, metadata_records: Iterable[SourceMetadataMapping]
    ) -> Mapping[str, type[object] | None]:
        """Infer ordered source literal types for one admitted source cohort."""
        types_by_name: dict[str, set[type[object]]] = {}
        for metadata in metadata_records:
            for name, value in cls.original_items(metadata):
                value_types = types_by_name.setdefault(name, set())
                if value is not None:
                    value_types.add(type(value))
        return MappingProxyType({
            name: next(iter(value_types)) if len(value_types) == 1 else None
            for name, value_types in types_by_name.items()
        })

    @classmethod
    def component_value(
        cls, metadata: SourceMetadataMapping, component: AllComponents
    ) -> str | None:
        return cls._view(
            metadata,
            component,
            lambda: SourceComponentProjectionStrategy.for_enum_member(
                component
            ).metadata_value(metadata),
        )

    @classmethod
    def _ordered_component_fields(
        cls, metadata: SourceMetadataMapping
    ) -> Iterator[tuple[AllComponents, SourceMetadataNonNullScalar]]:
        """Admit component fields once, with canonical spelling before aliases."""
        scalars = cls.scalar_items(metadata)
        cls.original_items(metadata)
        aliases: list[tuple[AllComponents, SourceMetadataNonNullScalar]] = []
        for name, value in scalars:
            if value is None:
                continue
            name = str(name)
            component = source_metadata_component(name)
            if component is None:
                continue
            item = (component, value)
            if name == component.value:
                yield item
            else:
                aliases.append(item)
        yield from aliases

    @classmethod
    def component_values(
        cls, metadata: SourceMetadataMapping, component: AllComponents
    ) -> tuple[str, ...]:
        """Read only the requested component from the current field admission."""
        return tuple(dict.fromkeys(
            str(value)
            for owner, value in cls._ordered_component_fields(metadata)
            if owner is component
        ))

    @classmethod
    def component_domains(
        cls, metadata: SourceMetadataMapping
    ) -> Mapping[AllComponents, tuple[str, ...]]:
        """Expand all ordered component domains from one current field admission."""
        domains: dict[AllComponents, list[str]] = {}
        for component, value in cls._ordered_component_fields(metadata):
            domains.setdefault(component, []).append(str(value))
        return {
            component: tuple(dict.fromkeys(values))
            for component, values in domains.items()
        }

    @staticmethod
    def readonly_snapshot(metadata: SourceMetadataMapping) -> SourceMetadataMapping:
        """Preserve the old mapping snapshot while retaining an owned record's lifetime."""
        if isinstance(metadata, SourceMetadataFields):
            return metadata._readonly_snapshot()
        return MappingProxyType(dict(metadata))

    def _readonly_snapshot(self) -> SourceMetadataMapping:
        return MappingProxyType(dict(self))

    @staticmethod
    def composition_snapshot(metadata: SourceMetadataMapping) -> SourceMetadataMapping:
        """Capture one composition's raw fields; owned records already hold that snapshot."""
        if isinstance(metadata, SourceMetadataFields):
            return metadata._composition_snapshot()
        return dict(metadata)

    def _composition_snapshot(self) -> SourceMetadataMapping:
        return dict(self)

    @staticmethod
    def derived_mapping(
        metadata: SourceMetadataMapping,
        fields: dict[str, SourceMetadataValue] | None,
    ) -> SourceMetadataMapping:
        """Keep owned lifetime on derived fields; raw callers receive a fresh dict."""
        if isinstance(metadata, SourceMetadataFields):
            return metadata._derive_fields(fields)
        return dict(metadata) if fields is None else fields

    def _derive_fields(
        self, fields: dict[str, SourceMetadataValue] | None
    ) -> SourceMetadataMapping:
        return dict(self) if fields is None else fields

    @classmethod
    def with_fields(
        cls,
        metadata: SourceMetadataMapping,
        updates: SourceMetadataMapping,
        *,
        without: Iterable[str] = (),
        components: Iterable[tuple[AllComponents, SourceMetadataScalar]] = (),
        after_components: SourceMetadataMapping | None = None,
    ) -> SourceMetadataMapping:
        excluded = frozenset(without)
        fields = {key: value for key, value in metadata.items() if key not in excluded}
        fields.update(updates)
        for component, value in components:
            fields = {
                key: field_value
                for key, field_value in fields.items()
                if key == ORIGINAL_SOURCE_METADATA_FIELD
                or source_metadata_component(str(key)) is not component
            }
            fields[component.value] = str(value)
        if after_components is not None:
            fields.update(after_components)
        return cls.derived_mapping(metadata, fields)

    @classmethod
    def with_component(
        cls,
        metadata: SourceMetadataMapping,
        component: AllComponents,
        value: SourceMetadataScalar,
    ) -> SourceMetadataMapping:
        return cls.with_fields(metadata, {}, components=((component, value),))

    @classmethod
    def with_missing_from(
        cls, metadata: SourceMetadataMapping, fallback: SourceMetadataMapping
    ) -> SourceMetadataMapping:
        merged: dict[str, SourceMetadataValue] | None = None
        current = metadata
        components = (
            ()
            if isinstance(metadata, SourceMetadataFields)
            and metadata._admitted_components_complete
            else AllComponents
        )
        for component in components:
            if cls.component_value(current, component) is not None:
                continue
            value = cls.component_value(fallback, component)
            if value is not None:
                if merged is None:
                    merged = dict(metadata)
                merged[component.value] = value
                current = merged
        if cls.literal_value(metadata, "extension") is None:
            extension = cls.literal_value(fallback, "extension")
            if extension is not None:
                if merged is None:
                    merged = dict(metadata)
                merged["extension"] = str(extension)
        if merged is None:
            return cls.derived_mapping(metadata, None)
        return cls.derived_mapping(metadata, merged)


@dataclass(frozen=True, slots=True, eq=False)
class SourceMetadataRecord(SourceMetadataFields):
    """Ordered source metadata carried through declared selector resolution."""

    @abstractmethod
    def resolve(
        self,
        path: str,
        parser: "FilenameParser",
        metadata_rules: tuple["MetadataExtractionRule", ...],
    ) -> "SourceMetadataRecord | None":
        """Resolve fields through their declared metadata lifetime."""

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SourceMetadataRecord):
            return NotImplemented
        return self.fields == other.fields

    def __hash__(self) -> int:
        return hash((self.fields,))


@dataclass(frozen=True, slots=True, eq=False)
class OwnedSourceMetadataFields(SourceMetadataFields):
    """Deep field ownership, indexed lookup, bounded views and local transport lifetime."""

    _field_index: Mapping[str, SourceMetadataValue] = field(
        init=False, repr=False, compare=False
    )
    _views: dict[str | AllComponents, object] = field(
        default_factory=dict, init=False, repr=False, compare=False
    )
    _cacheable: bool = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        fields = tuple(
            (str(key), self.normalized_value(value)) for key, value in self.fields
        )
        object.__setattr__(self, "fields", self._normalized_fields(fields))
        self._initialize_derived_views()

    @staticmethod
    def _normalized_fields(
        fields: tuple[tuple[str, SourceMetadataValue], ...],
    ) -> tuple[tuple[str, SourceMetadataValue], ...]:
        return fields

    def _initialize_derived_views(self) -> None:
        object.__setattr__(self, "_views", {})
        index: dict[str, SourceMetadataValue] = {}
        for key, value in self.fields:
            index.setdefault(key, value)
        object.__setattr__(self, "_field_index", MappingProxyType(index))
        object.__setattr__(
            self,
            "_cacheable",
            all(
                (
                    all(
                        type(v) in (str, int, float, bool, type(None))
                        for v in value.values()
                    )
                    if isinstance(value, Mapping)
                    else type(value) in (str, int, float, bool, type(None))
                )
                for _key, value in self.fields
            ),
        )

    def __reduce__(self):
        fields = tuple(
            (key, dict(value) if isinstance(value, Mapping) else value)
            for key, value in self.fields
        )
        return (type(self)._from_serialized_fields, (fields,))

    @classmethod
    def _from_serialized_fields(
        cls, fields: tuple[tuple[str, SourceMetadataValue], ...]
    ) -> Self:
        """Restore stored spelling and ownership without serializing derived views."""
        record = cls.__new__(cls)
        object.__setattr__(
            record,
            "fields",
            tuple(
                (
                    key,
                    (
                        MappingProxyType(dict(value))
                        if isinstance(value, Mapping)
                        else value
                    ),
                )
                for key, value in fields
            ),
        )
        record._initialize_derived_views()
        return record

    def __getitem__(self, key: str) -> SourceMetadataValue:
        return self._field_index[key]

    @property
    def metadata_contents(self) -> SourceMetadataMapping:
        """Read-only mapping contents, separate from ordered record equality."""
        return self._field_index

    def _derived_view(
        self, key: str | AllComponents, derive: Callable[[], _MetadataViewT]
    ) -> _MetadataViewT:
        if not self._cacheable:
            return derive()
        if key not in self._views:
            self._views[key] = derive()
        return self._views[key]

    @property
    def _admitted_components_complete(self) -> bool:
        return self._cacheable and all(
            self._views.get(component) is not None for component in AllComponents
        )

    def _literal_value(self, key: str) -> SourceMetadataScalar:
        if not self._cacheable:
            return super()._literal_value(key)

        def project() -> dict[str, SourceMetadataScalar]:
            scalars = SourceMetadataFields.scalar_items(self)
            original = SourceMetadataFields.original_items(self)
            values: dict[str, SourceMetadataScalar] = {}
            for fields in (original, scalars):
                for name, value in fields:
                    if value is not None:
                        values.setdefault(str(name), value)
            return values

        return self._derived_view("literal_values", project).get(key)

    def _readonly_snapshot(self) -> SourceMetadataMapping:
        return self

    def _composition_snapshot(self) -> SourceMetadataMapping:
        return self

    def _derive_fields(
        self, fields: dict[str, SourceMetadataValue] | None
    ) -> SourceMetadataMapping:
        return self if fields is None else DurableSourceMetadata.from_mapping(fields)


@dataclass(frozen=True, slots=True, eq=False)
class ResolvedSourceMetadataRecord(OwnedSourceMetadataFields, SourceMetadataRecord):
    """Owned runtime fields with the existing ordered selector record contract."""

    def _readonly_snapshot(self) -> SourceMetadataMapping:
        return self._derived_view(
            "readonly_snapshot",
            lambda: DurableSourceMetadata.from_mapping(self._field_index),
        )

    def resolve(
        self,
        path: str,
        parser: "FilenameParser",
        metadata_rules: tuple["MetadataExtractionRule", ...],
    ) -> SourceMetadataRecord | None:
        return self if self.fields else None


@dataclass(frozen=True, slots=True, eq=False)
class DurableSourceMetadata(OwnedSourceMetadataFields):
    """Owned literal metadata from durable storage and image field derivation."""

    @staticmethod
    def _normalized_fields(
        fields: tuple[tuple[str, SourceMetadataValue], ...],
    ) -> tuple[tuple[str, SourceMetadataValue], ...]:
        return tuple(dict(fields).items())

    def __eq__(self, other: object) -> bool:
        if isinstance(other, SourceMetadataRecord):
            return NotImplemented
        return Mapping.__eq__(self, other)

    __hash__ = None

    @staticmethod
    def _normalize_admitted_scalar(
        value: SourceMetadataNonNullScalar,
    ) -> SourceMetadataNonNullScalar:
        return value

    @staticmethod
    def _reject_scalar(value: object) -> NoReturn:
        if isinstance(value, Mapping) or (
            isinstance(value, Sequence) and not isinstance(value, str)
        ):
            raise RuntimeError(
                "virtual_workspace source metadata supports scalar values and "
                "one-level scalar mappings only."
            )
        raise RuntimeError(
            "virtual_workspace source metadata scalar values must be strings, "
            "numbers, booleans, or null."
        )


def source_metadata_dict(
    metadata: SourceMetadataMapping,
) -> dict[str, SourceMetadataValue]:
    """Return a detached JSON-compatible source-metadata mapping."""

    detached: dict[str, SourceMetadataValue] = {}
    for key, value in metadata.items():
        field = str(key)
        if field == ORIGINAL_SOURCE_METADATA_FIELD:
            detached[field] = OriginalSourceMetadata.from_reserved_value(
                value,
                path=field,
            ).as_dict()
        elif field == SOURCE_FILTER_PATHS_METADATA_FIELD:
            detached[field] = SourceFilterPathMetadata.from_reserved_value(
                value,
                path=field,
            ).as_dict()
        elif isinstance(value, Mapping):
            detached[field] = {
                str(nested_key): source_metadata_scalar(nested_value)
                for nested_key, nested_value in value.items()
            }
        else:
            detached[field] = source_metadata_scalar(value)
    return detached


def source_metadata_scalar(value: SourceMetadataScalar) -> SourceMetadataScalar:
    """Return the canonical scalar representation stored in source metadata."""

    return SourceMetadataFields.normalized_scalar(value)


def canonical_path_metadata_value(value: str) -> str:
    """Normalize absolute path values while leaving ordinary labels unchanged."""

    return _cached_canonical_path_metadata_value(value)


@lru_cache(maxsize=65536)
def _cached_canonical_path_metadata_value(value: str) -> str:
    """Return the canonical absolute path spelling for path-like metadata."""

    path = Path(value)
    if path.is_absolute():
        return str(path.resolve(strict=False))
    return value


def path_metadata_values_equivalent(left: str, right: str) -> bool:
    """Return whether two absolute path-like metadata values identify one path."""

    return _cached_path_metadata_values_equivalent(left, right)


@lru_cache(maxsize=65536)
def _cached_path_metadata_values_equivalent(left: str, right: str) -> bool:
    """Return cached absolute-path equivalence for source metadata values."""

    left_path = Path(left)
    right_path = Path(right)
    return (
        left_path.is_absolute()
        and right_path.is_absolute()
        and left_path.resolve(strict=False) == right_path.resolve(strict=False)
    )


@dataclass(frozen=True, slots=True)
class OriginalSourceMetadata:
    """Source-literal metadata preserved separately from canonical axis fields."""

    fields: tuple[tuple[str, SourceMetadataScalar], ...]

    @classmethod
    def from_mapping(
        cls,
        metadata: Mapping[str, SourceMetadataScalar],
    ) -> "OriginalSourceMetadata":
        return cls(
            tuple(
                (str(key), source_metadata_scalar(value))
                for key, value in metadata.items()
            )
        )

    @classmethod
    def from_reserved_value(
        cls,
        value: SourceMetadataValue,
        *,
        path: str,
    ) -> "OriginalSourceMetadata":
        if not isinstance(value, Mapping):
            raise RuntimeError(
                f"{ORIGINAL_SOURCE_METADATA_FIELD} for {path!r} must be a mapping, "
                f"got {type(value).__name__}: {value!r}."
            )
        return cls.from_mapping(value)

    def as_dict(self) -> dict[str, SourceMetadataScalar]:
        return dict(self.fields)

    def merge_into(
        self,
        target: dict[str, SourceMetadataValue],
        *,
        path: str,
    ) -> None:
        existing = target.get(ORIGINAL_SOURCE_METADATA_FIELD)
        merged = (
            {}
            if existing is None
            else OriginalSourceMetadata.from_reserved_value(
                existing,
                path=path,
            ).as_dict()
        )
        for key, value in self.fields:
            existing_value = merged.get(key)
            if (
                existing_value is not None
                and existing_value != value
                and not (
                    isinstance(existing_value, str)
                    and isinstance(value, str)
                    and path_metadata_values_equivalent(existing_value, value)
                )
            ):
                raise RuntimeError(
                    f"Conflicting original source metadata field {key!r} "
                    f"while parsing source candidate {path!r}: "
                    f"{existing_value!r} != {value!r}."
                )
            merged[key] = value
        target[ORIGINAL_SOURCE_METADATA_FIELD] = merged

    def overlay_into(
        self,
        target: dict[str, SourceMetadataValue],
        *,
        path: str,
    ) -> None:
        """Apply one later declared metadata stage over earlier literal fields."""

        existing = target.get(ORIGINAL_SOURCE_METADATA_FIELD)
        merged = (
            {}
            if existing is None
            else OriginalSourceMetadata.from_reserved_value(
                existing,
                path=path,
            ).as_dict()
        )
        merged.update(self.fields)
        target[ORIGINAL_SOURCE_METADATA_FIELD] = merged


@dataclass(frozen=True, slots=True)
class SourceFilterPathMetadata:
    """Source path identities that file selector clauses may target."""

    paths: tuple[str, ...]

    @classmethod
    def from_paths(
        cls,
        paths: tuple[str, ...],
    ) -> "SourceFilterPathMetadata":
        return cls(tuple(dict.fromkeys(str(path) for path in paths if str(path))))

    @classmethod
    def from_reserved_value(
        cls,
        value: SourceMetadataValue,
        *,
        path: str,
    ) -> "SourceFilterPathMetadata":
        if not isinstance(value, Mapping):
            raise RuntimeError(
                f"{SOURCE_FILTER_PATHS_METADATA_FIELD} for {path!r} must be a mapping, "
                f"got {type(value).__name__}."
            )
        return cls.from_paths(
            tuple(str(path_value) for _key, path_value in sorted(value.items()))
        )

    def as_dict(self) -> dict[str, str]:
        return {str(index): path for index, path in enumerate(self.paths)}

    def merge_into(
        self,
        target: dict[str, SourceMetadataValue],
        *,
        path: str,
    ) -> None:
        existing = target.get(SOURCE_FILTER_PATHS_METADATA_FIELD)
        merged = (
            ()
            if existing is None
            else SourceFilterPathMetadata.from_reserved_value(
                existing,
                path=path,
            ).paths
        )
        target[SOURCE_FILTER_PATHS_METADATA_FIELD] = (
            SourceFilterPathMetadata.from_paths((*merged, *self.paths)).as_dict()
        )


class SourceVoxelSpacingUnit(StrEnum):
    """Coordinate units own their projection into physical scalar calibration."""

    native_unit: str

    MICROMETERS = (
        "micrometers",
        lambda spacing: spacing.isotropic_xy_spacing,
        "micrometer",
        lambda spacing: spacing.values_zyx,
    )
    RELATIVE = "relative", lambda spacing: None, "dimensionless", lambda spacing: None
    PIXELS = "pixels", lambda spacing: None, "pixel", lambda spacing: None

    def __new__(
        cls,
        name: str,
        physical_projection: Callable[["SourceVoxelSpacing"], float | None],
        native_unit: str,
        physical_coordinates: Callable[["SourceVoxelSpacing"], tuple[float, ...] | None],
    ):
        member = str.__new__(cls, name)
        member._value_ = name
        member._physical_projection = physical_projection
        member.native_unit = native_unit
        member._physical_coordinates = physical_coordinates
        return member

    def physical_pixel_size(self, spacing: "SourceVoxelSpacing") -> float | None:
        return self._physical_projection(spacing)

    def physical_coordinates(self, spacing: "SourceVoxelSpacing") -> tuple[float, ...] | None:
        """Project coordinates only when this declaration establishes physical units."""
        return self._physical_coordinates(spacing)


@dataclass(frozen=True, slots=True)
class SourceVoxelSpacing:
    """Source-pixel coordinates, ordered like arrays, with explicit unit semantics.

    Configured values are micrometers. CellProfiler NamesAndTypes coordinates are
    dimensionless ratios normalized by Y, not absolute physical calibration.
    """

    values_zyx: tuple[float, ...] = ()
    """Positive y/x or z/y/x spacing values; an empty tuple means unspecified spacing."""

    unit: SourceVoxelSpacingUnit = SourceVoxelSpacingUnit.MICROMETERS
    """Units of the configured spacing values.

    MICROMETERS specifies physical micrometers per pixel. Physical scalar
    measurements require equal X and Y spacing and consistent calibration across
    their image sources; Z spacing may differ. RELATIVE specifies dimensionless
    coordinate ratios, including CellProfiler spacing normalized by Y. Relative
    spacing and legacy spacing metadata without recorded units do not provide
    physical scalar calibration. An empty values tuple leaves spacing unspecified.
    PIXELS explicitly measures source-pixel coordinates; it does not establish
    physical calibration or authorize physical coordinate exports.
    """

    def __post_init__(self) -> None:
        normalized = tuple(float(value) for value in self.values_zyx)
        if any(not isfinite(value) or value <= 0 for value in normalized):
            raise ValueError("SourceVoxelSpacing values must be finite and positive.")
        if len(normalized) not in (0, 2, 3):
            raise ValueError(
                "SourceVoxelSpacing requires 2-D or 3-D spacing, got "
                f"{len(normalized)} values."
            )
        object.__setattr__(self, "values_zyx", normalized)
        if not isinstance(self.unit, SourceVoxelSpacingUnit):
            raise TypeError("SourceVoxelSpacing.unit must be SourceVoxelSpacingUnit.")

    @classmethod
    def coerce(
        cls, value: "SourceVoxelSpacing | Sequence[float]"
    ) -> "SourceVoxelSpacing":
        """Retain nominal spacing or validate authored coordinate values."""
        return value if isinstance(value, cls) else cls(tuple(value))

    @property
    def has_values(self) -> bool:
        return bool(self.values_zyx)

    @classmethod
    def from_cellprofiler_xyz(
        cls,
        *,
        x: float,
        y: float,
        z: float,
    ) -> "SourceVoxelSpacing":
        """Return CellProfiler Image.spacing semantics from NamesAndTypes values."""
        raw_y = float(y)
        if raw_y <= 0:
            raise ValueError(
                "CellProfiler relative pixel spacing in Y must be positive."
            )
        return cls(
            (float(z) / raw_y, 1.0, float(x) / raw_y),
            unit=SourceVoxelSpacingUnit.RELATIVE,
        )

    @classmethod
    def from_source_metadata(
        cls,
        metadata: SourceMetadataMapping | None,
    ) -> "SourceVoxelSpacing":
        if metadata is None:
            return cls()
        value = metadata.get(SOURCE_VOXEL_SPACING_FIELD)
        if value is None:
            return cls()
        if isinstance(value, Mapping):
            values = tuple(
                float(value[axis])
                for axis in ("z", "y", "x")
                if axis in value and value[axis] is not None
            )
        else:
            values = tuple(
                float(part) for part in str(value).split(",") if part.strip()
            )
        # Historical coordinate metadata did not establish physical units.
        unit = SourceVoxelSpacingUnit(
            metadata.get(
                SOURCE_VOXEL_SPACING_UNIT_FIELD, SourceVoxelSpacingUnit.RELATIVE.value
            )
        )
        return cls(values, unit=unit)

    @property
    def isotropic_xy_spacing(self) -> float | None:
        if not self.has_values:
            return None
        y, x = self.values_zyx[-2:]
        return x if x == y else None

    @classmethod
    def common_physical_pixel_size(
        cls, spacings: Iterable["SourceVoxelSpacing"]
    ) -> float | None:
        """Project a uniformly calibrated source set; Z need not equal X/Y."""
        values = tuple(
            spacing.unit.physical_pixel_size(spacing) for spacing in spacings
        )
        unique = set(values)
        return values[0] if len(unique) == 1 and None not in unique else None

    @classmethod
    def common(cls, spacings: Iterable["SourceVoxelSpacing"]) -> "SourceVoxelSpacing":
        """Return a shared declared frame; absent/conflicting sources imply none.

        Numeric metadata compatibility values never establish a source frame.
        Individual payload declarations remain authoritative when frames differ.
        """
        from openhcs.core.source_spatial_domain import CommonRuntimeValue

        spacing = CommonRuntimeValue.from_values(spacings).single
        return cls() if spacing is None else spacing

    @classmethod
    def metadata_pixel_size(cls, spacings: Iterable["SourceVoxelSpacing"]) -> float:
        """Numeric legacy metadata view; physical artifacts validate coordinates.

        The existing uncalibrated compatibility value remains 1.0 where no
        uniform physical scalar exists. It does not establish micrometer units.
        """
        value = cls.common_physical_pixel_size(spacings)
        return 1.0 if value is None else value

    @classmethod
    def require_physical_pixel_size(
        cls, spacings: Iterable["SourceVoxelSpacing"]
    ) -> float:
        value = cls.common_physical_pixel_size(spacings)
        if value is None:
            raise ValueError(
                "Physical scalar pixel size requires micrometer calibration, "
                "isotropic X/Y spacing, and agreement across every source. "
                "Relative coordinates and mixed or conflicting calibrations "
                "cannot provide this artifact."
            )
        return value

    def require_physical_coordinates(self) -> tuple[float, ...]:
        """Admit physical exports without treating pixel or relative units as micrometers."""
        coordinates = self.unit.physical_coordinates(self)
        if not coordinates:
            raise ValueError(
                "Physical coordinate export requires explicit micrometer spacing; "
                "pixel and relative analysis coordinates cannot provide it."
            )
        return coordinates

    def as_source_metadata_value(self) -> str:
        return ",".join(f"{value:.17g}" for value in self.values_zyx)

    def merge_into(
        self,
        target: dict[str, SourceMetadataValue],
        *,
        path: str,
    ) -> None:
        if not self.has_values:
            return
        existing = SourceVoxelSpacing.from_source_metadata(target)
        if existing.has_values and existing != self:
            raise RuntimeError(
                f"Conflicting source voxel spacing while parsing source candidate "
                f"{path!r}: {existing.values_zyx!r} != {self.values_zyx!r}."
            )
        target[SOURCE_VOXEL_SPACING_FIELD] = self.as_source_metadata_value()
        target[SOURCE_VOXEL_SPACING_UNIT_FIELD] = self.unit.value

    def with_missing_from(
        self,
        fallback: "SourceVoxelSpacing",
    ) -> "SourceVoxelSpacing":
        if self.has_values:
            return self
        return fallback

    def spacing_for_ndim(self, ndim: int) -> tuple[float, ...]:
        if ndim <= 0:
            raise ValueError("SourceVoxelSpacing ndim must be positive.")
        if not self.has_values:
            return (1.0,) * ndim
        if ndim > len(self.values_zyx):
            raise ValueError(
                f"Cannot project {len(self.values_zyx)}-D source voxel spacing "
                f"onto {ndim}-D data."
            )
        return self.values_zyx[-ndim:]

    def layer_coordinate_kwargs(
        self, axis_labels: Sequence[str]
    ) -> dict[str, tuple[float, ...] | tuple[str, ...]]:
        """Project source calibration onto semantic layer axes and payload bands."""
        labels = tuple(axis_labels)
        if (
            len(labels) < 2
            or labels[-2:] != ("y", "x")
            or len(set(labels)) != len(labels)
        ):
            raise ValueError(
                "Source calibration requires unique semantic axes ending in Y/X."
            )
        scale = [1.0] * len(labels)
        units = ["dimensionless"] * len(labels)
        scale[-2:] = self.spacing_for_ndim(2)
        units[-2:] = (self.native_coordinate_unit,) * 2
        z_component = AllComponents.Z_INDEX.value
        if len(self.values_zyx) == 3 and z_component in labels:
            z_axis = labels.index(z_component)
            scale[z_axis] = self.spacing_for_ndim(3)[0]
            units[z_axis] = self.native_coordinate_unit
        return {"scale": tuple(scale), "units": tuple(units)}

    @property
    def native_coordinate_unit(self) -> str:
        """Unknown calibration is pixels, never an inferred physical unit."""
        return self.unit.native_unit if self.has_values else "pixel"


@dataclass(kw_only=True)
class SourceVoxelSpacingFields:
    """Source-image voxel spacing carried by runtime payload metadata."""

    source_voxel_spacing: SourceVoxelSpacing = field(
        default_factory=SourceVoxelSpacing,
        metadata={ViewerWireField.IMAGE_METADATA: True},
    )

    def normalize_source_voxel_spacing_fields(self) -> None:
        self.source_voxel_spacing = SourceVoxelSpacing.coerce(self.source_voxel_spacing)


@lru_cache(maxsize=4096)
def source_metadata_field_identity(field: str) -> str:
    """Return the canonical semantic identity of one source metadata field."""

    normalized = "".join(
        character for character in field.lower() if character.isalnum()
    )
    return (
        normalized.removeprefix("metadata")
        if normalized.startswith("metadata")
        else normalized
    )


@lru_cache(maxsize=256)
def source_metadata_component(field: str) -> AllComponents | None:
    """Return the nominal component owner of a metadata field."""
    return SourceComponentProjectionStrategy.component_for_metadata_field(field)


class SourceComponentProjectionStrategy(
    EnumKeyedStrategyMixin[AllComponents],
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Project one OpenHCS component through its nominal enum-owned leaf."""

    strategy_key: ClassVar[AllComponents | None] = None
    metadata_collection_field: ClassVar[str]
    metadata_field_groups: ClassVar[tuple[tuple[str, ...], ...]] = ()

    @classmethod
    def project_component(
        cls,
        component: AllComponents,
        metadata: SourceMetadataMapping,
        image_set_index: int,
    ) -> str:
        return cls.for_enum_member(component).project(metadata, image_set_index)

    @classmethod
    def metadata_component(
        cls,
        component: AllComponents,
        metadata: SourceMetadataMapping,
    ) -> str | None:
        return SourceMetadataFields.component_value(metadata, component)

    @classmethod
    def component_for_metadata_field(
        cls,
        field: str,
    ) -> AllComponents | None:
        owners = tuple(
            strategy_type.strategy_key
            for strategy_type in cls.registered_strategy_types()
            if strategy_type.owns_metadata_field(field)
        )
        if len(owners) > 1:
            raise RuntimeError(
                f"Source metadata field {field!r} has multiple component owners: "
                f"{owners!r}."
            )
        return owners[0] if owners else None

    @classmethod
    def owns_metadata_field(cls, field: str) -> bool:
        normalized = source_metadata_field_identity(field)
        return any(
            normalized == source_metadata_field_identity(alias)
            for group in cls.metadata_field_groups
            for alias in group
        )

    @classmethod
    def _metadata_group_value(
        cls,
        metadata: SourceMetadataMapping,
        group: tuple[str, ...],
    ) -> str | None:
        scalar_items = SourceMetadataFields.scalar_items(metadata)
        for alias in group:
            alias_identity = source_metadata_field_identity(alias)
            for field_name, value in scalar_items:
                if (
                    value is not None
                    and source_metadata_field_identity(field_name) == alias_identity
                ):
                    return str(value)
        return None

    def metadata_value(self, metadata: SourceMetadataMapping) -> str | None:
        if len(self.metadata_field_groups) != 1:
            raise RuntimeError(
                f"{type(self).__name__} must implement metadata_value() for "
                f"{len(self.metadata_field_groups)} metadata field groups."
            )
        return self._metadata_group_value(metadata, self.metadata_field_groups[0])

    @abstractmethod
    def project(
        self,
        metadata: SourceMetadataMapping,
        image_set_index: int,
    ) -> str:
        """Return one canonical component value."""


class WellSourceComponentProjection(SourceComponentProjectionStrategy):
    strategy_key = AllComponents.WELL
    metadata_collection_field = "wells"
    metadata_field_groups = (
        ("well",),
        ("wellrow", "row"),
        ("wellcolumn", "wellcol", "column", "col"),
    )

    def metadata_value(self, metadata: SourceMetadataMapping) -> str | None:
        direct = self._metadata_group_value(metadata, self.metadata_field_groups[0])
        if direct is not None:
            return direct
        row = self._metadata_group_value(metadata, self.metadata_field_groups[1])
        column = self._metadata_group_value(metadata, self.metadata_field_groups[2])
        if row is None or column is None:
            return None
        return f"{row.strip().upper()}{int(column):02d}"

    def project(
        self,
        metadata: SourceMetadataMapping,
        image_set_index: int,
    ) -> str:
        del image_set_index
        return self.metadata_value(metadata) or "A01"


class SiteSourceComponentProjection(SourceComponentProjectionStrategy):
    strategy_key = AllComponents.SITE
    metadata_collection_field = "sites"
    metadata_field_groups = (("site", "imagenumber"),)

    def project(
        self,
        metadata: SourceMetadataMapping,
        image_set_index: int,
    ) -> str:
        direct = self.metadata_value(metadata)
        if direct is not None:
            return direct
        if any(
            SourceComponentProjectionStrategy.metadata_component(component, metadata)
            is not None
            for component in (AllComponents.Z_INDEX, AllComponents.TIMEPOINT)
        ):
            return "1"
        return str(image_set_index + 1)


class ChannelSourceComponentProjection(SourceComponentProjectionStrategy):
    strategy_key = AllComponents.CHANNEL
    metadata_collection_field = "channels"
    metadata_field_groups = (("channel", "channelnumber"),)

    def project(
        self,
        metadata: SourceMetadataMapping,
        image_set_index: int,
    ) -> str:
        return self.metadata_value(metadata) or str(image_set_index + 1)


class ZIndexSourceComponentProjection(SourceComponentProjectionStrategy):
    strategy_key = AllComponents.Z_INDEX
    metadata_collection_field = "z_indexes"
    metadata_field_groups = (("zindex", "z", "zplane", "zslice", "plane", "slice"),)

    def project(
        self,
        metadata: SourceMetadataMapping,
        image_set_index: int,
    ) -> str:
        del image_set_index
        return self.metadata_value(metadata) or "1"


class TimepointSourceComponentProjection(SourceComponentProjectionStrategy):
    strategy_key = AllComponents.TIMEPOINT
    metadata_collection_field = "timepoints"
    metadata_field_groups = (("timepoint", "time", "framenumber", "frame"),)

    def project(
        self,
        metadata: SourceMetadataMapping,
        image_set_index: int,
    ) -> str:
        del image_set_index
        return self.metadata_value(metadata) or "1"
