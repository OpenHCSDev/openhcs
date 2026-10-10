"""Source-image provenance identity shared by runtime payload carriers."""

from __future__ import annotations

import json
from abc import ABC, abstractmethod
from collections.abc import Callable, Iterable, Sequence, Mapping
from dataclasses import InitVar, dataclass, field, replace
from pathlib import Path
from inspect import signature
from math import isfinite
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, ClassVar, Generic, Self, TypeVar, get_type_hints

from metaclass_registry import AutoRegisterMeta
from python_introspect.validation import validate_annotation_value
from python_introspect import to_jsonable

from openhcs.core.source_metadata import (
    SOURCE_PLANE_COUNT_FIELD,
    SOURCE_PLANE_INDEX_FIELD,
    OwnedSourceMetadataFields,
    SourceMetadataFields,
    SourceMetadataMapping,
    SourceMetadataScalar,
    SourceMetadataValue,
)
from openhcs.core.source_matching import (
    SourceImageSetIdentity,
    SourceImageSetIdentityPolicy,
    source_component_metadata_raw_value,
    source_component_metadata_value,
    source_metadata_value,
    with_source_component_metadata,
)
from openhcs.core.axes import Axis, AxisFamily, StackAxis

SourceComponentMetadata = SourceMetadataMapping
SourceImageProvenancePlanePathValues = tuple[str | None, ...]
SourceImageProvenancePlaneMetadataValues = tuple[SourceComponentMetadata | None, ...]
SourceProvenanceIdentity = tuple[str | None, tuple[tuple[str, str], ...] | None]
SourceImageProvenancePlaneIdentity = tuple[
    str,
    SourceProvenanceIdentity,
    str | None,
    tuple["SourceImageProvenancePlaneIdentity", ...],
]
SourceImageProvenanceIdentity = tuple[
    SourceProvenanceIdentity,
    tuple[SourceImageProvenancePlaneIdentity, ...],
    tuple[str, ...],
]
SourceProvenanceInitValues = tuple[
    str | None,
    SourceComponentMetadata | None,
    "SourceImageProvenancePlanes",
    tuple[str, ...],
]

SourceImageProvenanceAliasValueT = TypeVar("SourceImageProvenanceAliasValueT")
SourceImageProvenancePlaneValueT = TypeVar("SourceImageProvenancePlaneValueT")

if TYPE_CHECKING:
    from openhcs.core.dataset_sources.interfaces import FilenameParser


def normalize_source_path(source_path: str | None) -> str | None:
    """Normalize path-like source identities to their stored scalar value."""
    if source_path is None:
        return None
    return str(source_path)


def _component_metadata_identity(
    metadata: SourceComponentMetadata | None,
) -> tuple[tuple[str, str], ...] | None:
    if metadata is None:
        return None
    return SourceMetadataFields.provenance_identity_items(metadata)


def _tuple_value(values: tuple[Any, ...], index: int) -> Any | None:
    if 0 <= index < len(values):
        return values[index]
    return None


@dataclass(slots=True)
class SourceImageIdentity:
    """Scalar source-image address from path and parsed component metadata."""

    path: str | None = None
    component_metadata: SourceComponentMetadata | None = None
    _identity: SourceProvenanceIdentity = field(init=False, repr=False)

    def __post_init__(self) -> None:
        self.path = normalize_source_path(self.path)
        if self.component_metadata is not None:
            self.component_metadata = SourceMetadataFields.readonly_snapshot(
                self.component_metadata
            )
        self._identity = (
            self.path,
            _component_metadata_identity(self.component_metadata),
        )

    @classmethod
    def from_mapping(cls, values: Mapping[str, object]) -> "SourceImageIdentity":
        """Admit current wire facts, with independent nested metadata ownership."""
        if not isinstance(values, Mapping):
            raise TypeError("Source image identity must be a mapping.")
        unknown = set(values) - {"path", "component_metadata"}
        if unknown:
            raise ValueError(f"Unknown source identity fields: {sorted(unknown)!r}.")
        path = values.get("path")
        metadata = values.get("component_metadata")
        validate_annotation_value(str | None, path, path="SourceImageIdentity.path")
        validate_annotation_value(
            SourceComponentMetadata | None,
            metadata,
            path="SourceImageIdentity.component_metadata",
        )
        return cls(path, to_jsonable(metadata))

    @property
    def addressable(self) -> bool:
        return self.path is not None or self.component_metadata is not None

    @property
    def filename_extension(self) -> str | None:
        """Project the declared source filename fact, never a format default."""
        if self.component_metadata is None:
            return None
        extension = source_metadata_value(self.component_metadata, "extension")
        return None if extension is None else str(extension)

    @property
    def identity(self) -> SourceProvenanceIdentity:
        if not hasattr(self, "_identity"):
            self._identity = (
                self.path,
                _component_metadata_identity(self.component_metadata),
            )
        return self._identity

    def with_missing_from(
        self,
        fallback: "SourceImageIdentity",
    ) -> "SourceImageIdentity":
        return type(self)(
            path=self.path if self.path is not None else fallback.path,
            component_metadata=self.component_metadata_with_missing_from(fallback),
        )

    def image_set_identities(
        self,
        policy: SourceImageSetIdentityPolicy,
    ) -> frozenset[SourceImageSetIdentity]:
        """Project this scalar source address into its declared image-set domain."""
        identity = SourceImageSetIdentity.from_metadata(
            self.component_metadata or {},
            fallback_source_path=self.path or "",
            policy=policy,
        )
        return (
            frozenset()
            if identity.components == (("source_path", ""),)
            else frozenset((identity,))
        )

    def component_metadata_with_missing_from(
        self,
        fallback: "SourceImageIdentity",
    ) -> SourceComponentMetadata | None:
        """Fill missing address components and its declared file extension."""
        if self.component_metadata is None:
            return fallback.component_metadata
        if fallback.component_metadata is None:
            return self.component_metadata

        merged = SourceMetadataFields.with_missing_from(
            self.component_metadata, fallback.component_metadata
        )
        return SourceMetadataFields.readonly_snapshot(merged)

    def with_parsed_path_components(
        self,
        parser: "FilenameParser",
    ) -> "SourceImageIdentity":
        """Fill missing component metadata from this identity's source path."""
        if self.path is None:
            return self
        parsed = parser.parse_filename(Path(self.path).name)
        if parsed is None:
            return self
        return self.with_missing_from(
            type(self)(component_metadata=parsed.wire_mapping())
        )


@dataclass(slots=True)
class SourceImageProvenancePlane(ABC, metaclass=AutoRegisterMeta):
    """Nominal source identity contributing to a runtime image payload."""

    __registry_key__ = "identity_kind"
    __skip_if_no_key__ = True
    identity_kind: ClassVar[str | None] = None
    source_identity: SourceImageIdentity = field(default_factory=SourceImageIdentity)
    contributors: tuple["SourceImageProvenanceContributor", ...] = ()
    source_image_name: str | None = None

    def __post_init__(self) -> None:
        self.contributors = tuple(self.contributors)
        if any(
            not isinstance(contributor, SourceImageProvenanceContributor)
            for contributor in self.contributors
        ):
            raise TypeError(
                "Source-image provenance contributors must use the nominal "
                "SourceImageProvenanceContributor type."
            )

    @classmethod
    def from_mapping(
        cls,
        values: Mapping[str, object],
        identities: Sequence[Mapping[str, object]] | None = None,
    ) -> "SourceImageProvenancePlane":
        """Decode nominal planes from current references or historic flat facts."""
        if not isinstance(values, Mapping):
            raise TypeError("Source provenance plane must be a mapping.")
        fields = {"identity_kind", "source_image_name", "contributors"}
        fields.update(
            {"path", "component_metadata"} if identities is None else {"identity"}
        )
        unknown = set(values) - fields
        if unknown:
            raise ValueError(f"Unknown provenance plane fields: {sorted(unknown)!r}.")
        kind = values.get(
            "identity_kind",
            RuntimeSourceImageProvenancePlane.identity_kind if identities is None else None,
        )
        if not isinstance(kind, str) or kind not in cls.__registry__:
            raise ValueError(f"Unknown source-image provenance identity kind {kind!r}.")
        name = values.get("source_image_name")
        validate_annotation_value(
            str | None, name, path="SourceProvenancePlane.source_image_name"
        )
        contributors = values.get("contributors", ())
        if not isinstance(contributors, Sequence) or isinstance(
            contributors, (str, bytes, bytearray)
        ):
            raise TypeError("Source provenance contributors must be a sequence.")
        if identities is None:
            facts = {
                key: values[key] for key in ("path", "component_metadata") if key in values
            }
        else:
            index = values.get("identity")
            if type(index) is not int or not 0 <= index < len(identities):
                raise ValueError(
                    f"Invalid source-image provenance identity index {index!r}."
                )
            facts = identities[index]
        return cls.__registry__[kind](
            SourceImageIdentity.from_mapping(facts),
            tuple(cls.from_mapping(item, identities) for item in contributors),
            name,
        )

    @property
    def path(self) -> str | None:
        return self.source_identity.path

    @property
    def component_metadata(self) -> SourceComponentMetadata | None:
        return self.source_identity.component_metadata

    @property
    def addressable(self) -> bool:
        return self.source_identity.addressable or (
            bool(self.contributors)
            and all(contributor.addressable for contributor in self.contributors)
        )

    @property
    def represented_source_image_names(self) -> tuple[str, ...]:
        """Return every source-image name represented by this plane."""

        return tuple(
            dict.fromkeys(
                name
                for name in (
                    self.source_image_name,
                    *(
                        contributor.source_image_name
                        for contributor in self.contributors
                    ),
                )
                if name is not None
            )
        )

    @property
    def identity(self) -> SourceImageProvenancePlaneIdentity:
        if self.identity_kind is None:
            raise TypeError(
                f"{type(self).__name__} has no source-provenance identity kind."
            )
        return (
            self.identity_kind,
            self.source_identity.identity,
            self.source_image_name,
            tuple(contributor.identity for contributor in self.contributors),
        )

    def source_identity_for_name(self, source_image_name: str) -> SourceImageIdentity:
        """Return the exact source identity owned by one declared image name."""

        if self.source_image_name == source_image_name:
            return self.source_identity
        matches = tuple(
            contributor.source_identity
            for contributor in self.contributors
            if contributor.source_image_name == source_image_name
        )
        if len(matches) != 1:
            raise ValueError(
                "Source provenance plane must declare exactly one identity for "
                f"source image {source_image_name!r}; found {len(matches)} in "
                f"{self.represented_source_image_names!r}."
            )
        return matches[0]

    def with_missing_from(
        self,
        fallback: "SourceImageProvenancePlane",
    ) -> "SourceImageProvenancePlane":
        return type(self)(
            self.source_identity.with_missing_from(fallback.source_identity),
            self.contributors or fallback.contributors,
            self.source_image_name or fallback.source_image_name,
        )


@dataclass(slots=True)
class RuntimeSourceImageProvenancePlane(SourceImageProvenancePlane):
    """Source identity owned by one projectable runtime payload plane."""

    identity_kind = "runtime_plane"


@dataclass(slots=True)
class SourceImageProvenanceContributor(SourceImageProvenancePlane):
    """Source identity contributing pixels without owning a runtime plane."""

    identity_kind = "pixel_contributor"

    def __post_init__(self) -> None:
        SourceImageProvenancePlane.__post_init__(self)
        if self.contributors:
            raise ValueError(
                "Source-image pixel contributors cannot contain nested contributors."
            )

    def with_missing_from(
        self,
        fallback: "SourceImageProvenancePlane",
    ) -> "SourceImageProvenanceContributor":
        """Fill this leaf contributor without importing fallback topology."""

        return type(self)(
            self.source_identity.with_missing_from(fallback.source_identity),
            source_image_name=self.source_image_name or fallback.source_image_name,
        )


@dataclass(slots=True)
class SourceImageProvenancePlanes:
    """Nominal carrier for runtime-plane and pixel-contributor provenance."""

    planes: tuple[SourceImageProvenancePlane, ...] = ()
    _paths: SourceImageProvenancePlanePathValues = field(init=False, repr=False)
    _component_metadata: SourceImageProvenancePlaneMetadataValues = field(
        init=False,
        repr=False,
    )
    _identity: tuple[SourceImageProvenancePlaneIdentity, ...] = field(
        init=False,
        repr=False,
    )
    _runtime_planes: tuple[RuntimeSourceImageProvenancePlane, ...] = field(
        init=False,
        repr=False,
    )

    def __post_init__(self) -> None:
        self.planes = tuple(self.planes)
        invalid_plane_types = tuple(
            type(plane).__name__
            for plane in self.planes
            if not isinstance(plane, SourceImageProvenancePlane)
        )
        if invalid_plane_types:
            raise TypeError(
                "Source-image provenance planes must use the nominal "
                "SourceImageProvenancePlane hierarchy, got "
                f"{invalid_plane_types!r}."
            )
        self._paths = tuple(plane.path for plane in self.planes)
        self._component_metadata = tuple(
            plane.component_metadata for plane in self.planes
        )
        self._identity = tuple(plane.identity for plane in self.planes)
        self._runtime_planes = tuple(
            plane
            for plane in self.planes
            if isinstance(plane, RuntimeSourceImageProvenancePlane)
        )

    @classmethod
    def from_components(
        cls,
        *,
        paths: SourceImageProvenancePlanePathValues = (),
        component_metadata: SourceImageProvenancePlaneMetadataValues = (),
    ) -> "SourceImageProvenancePlanes":
        count = max(len(paths), len(component_metadata), 0)
        return cls(
            tuple(
                RuntimeSourceImageProvenancePlane(
                    SourceImageIdentity(
                        path=_tuple_value(paths, index),
                        component_metadata=_tuple_value(component_metadata, index),
                    )
                )
                for index in range(count)
            )
        )

    @classmethod
    def from_component_domain(
        cls,
        *,
        path: str,
        fixed_components: SourceComponentMetadata,
        aggregate_components: Mapping[str, Sequence[SourceMetadataScalar]],
        plane_count: int,
    ) -> "SourceImageProvenancePlanes":
        """Expand one explicitly ordered varying coordinate into runtime planes.

        Neither filenames, page counts, nor plate cardinalities establish this
        coordinate domain. The caller must supply its original declaration.
        """
        component_names = frozenset(AxisFamily.active().names())
        if (
            len(aggregate_components) != 1
            or set(fixed_components) & set(aggregate_components)
            or set(fixed_components) | set(aggregate_components) != component_names
            or type(plane_count) is not int
            or plane_count <= 0
        ):
            raise ValueError(
                "Image plane domain requires complete disjoint components."
            )
        varying_component, declared_values = next(iter(aggregate_components.items()))
        if not isinstance(declared_values, Sequence) or isinstance(
            declared_values, str
        ):
            raise TypeError(
                "Image plane domain requires an ordered coordinate sequence."
            )
        values = tuple(declared_values)
        coordinates = (*fixed_components.values(), *values)
        if any(
            not isinstance(value, (str, int, float))
            or isinstance(value, bool)
            or (isinstance(value, str) and not value)
            or (isinstance(value, float) and not isfinite(value))
            for value in coordinates
        ):
            raise ValueError("Image plane coordinates must be finite nonempty scalars.")
        if (
            len(values) != plane_count
            or len(set(values)) != plane_count
            or len(set(map(str, values))) != plane_count
        ):
            raise ValueError(
                "Image plane domain cardinality or unique ordering conflicts."
            )
        return cls.from_components(
            paths=(path,) * plane_count,
            component_metadata=tuple(
                {**fixed_components, varying_component: value} for value in values
            ),
        )

    @classmethod
    def from_contributor_components(
        cls,
        *,
        paths: SourceImageProvenancePlanePathValues = (),
        component_metadata: SourceImageProvenancePlaneMetadataValues = (),
    ) -> "SourceImageProvenancePlanes":
        """Build non-projectable pixel contributors from scalar identities."""
        count = max(len(paths), len(component_metadata), 0)
        return cls(
            tuple(
                SourceImageProvenanceContributor(
                    SourceImageIdentity(
                        path=_tuple_value(paths, index),
                        component_metadata=_tuple_value(component_metadata, index),
                    )
                )
                for index in range(count)
            )
        )

    @classmethod
    def from_mapping(cls, values: object) -> "SourceImageProvenancePlanes":
        """Admit factored current wire or the historic flat persisted sequence."""
        if isinstance(values, Mapping):
            if set(values) != {"identities", "planes"}:
                raise ValueError(
                    "Factored provenance requires exactly identities and planes."
                )
            identities = values["identities"]
            planes = values["planes"]
            if not isinstance(identities, Sequence) or isinstance(
                identities, (str, bytes, bytearray)
            ):
                raise TypeError("Source provenance identities must be a sequence.")
            # Validate even unreferenced facts; references never weaken admission.
            for facts in identities:
                SourceImageIdentity.from_mapping(facts)
        else:
            identities = None
            planes = values
        if not isinstance(planes, Sequence) or isinstance(planes, (str, bytes, bytearray)):
            raise TypeError("Source provenance planes must be a sequence.")
        return cls(
            tuple(
                SourceImageProvenancePlane.from_mapping(item, identities) for item in planes
            )
        )

    def to_mapping(self) -> dict[str, object]:
        """Snapshot current identity facts once locally, retaining ordered aliases.

        The mutable birth fingerprint is intentionally not a wire grouping key.
        Full current JSON facts decide equality only within this serialization.
        """
        object_indices: dict[int, int] = {}
        fact_indices: dict[str, int] = {}
        identities: list[dict[str, object]] = []

        def record(plane: SourceImageProvenancePlane) -> dict[str, object]:
            identity = plane.source_identity
            marker = id(identity)
            if marker not in object_indices:
                facts = {
                    "path": identity.path,
                    "component_metadata": to_jsonable(identity.component_metadata),
                }
                canonical = json.dumps(facts, sort_keys=True, separators=(",", ":"))
                if canonical not in fact_indices:
                    fact_indices[canonical] = len(identities)
                    identities.append(facts)
                object_indices[marker] = fact_indices[canonical]
            return {
                "identity": object_indices[marker],
                "identity_kind": plane.identity_kind,
                "source_image_name": plane.source_image_name,
                "contributors": [record(item) for item in plane.contributors],
            }

        return {
            "identities": identities,
            "planes": [record(plane) for plane in self.planes],
        }

    @property
    def paths(self) -> SourceImageProvenancePlanePathValues:
        self._ensure_identity_cache()
        return self._paths

    @property
    def component_metadata(self) -> SourceImageProvenancePlaneMetadataValues:
        self._ensure_identity_cache()
        return self._component_metadata

    @property
    def runtime_component_metadata(
        self,
    ) -> SourceImageProvenancePlaneMetadataValues:
        """Return component metadata for projectable runtime planes only."""
        self._ensure_identity_cache()
        return tuple(plane.component_metadata for plane in self._runtime_planes)

    @property
    def count(self) -> int:
        """Return projectable runtime-plane cardinality."""
        self._ensure_identity_cache()
        return len(self._runtime_planes)

    @property
    def identity_count(self) -> int:
        """Return all top-level provenance identities, including contributors."""
        return len(self.planes)

    @property
    def contributors(self) -> tuple[SourceImageProvenanceContributor, ...]:
        """Return all direct and runtime-plane-nested pixel contributors."""
        return tuple(
            contributor
            for plane in self.planes
            for contributor in (
                (plane,)
                if isinstance(plane, SourceImageProvenanceContributor)
                else plane.contributors
            )
        )

    @property
    def represented_source_image_names(self) -> tuple[str, ...]:
        """Return every alias owned by a runtime plane or pixel contributor."""

        return tuple(
            dict.fromkeys(
                name
                for plane in self.planes
                for name in plane.represented_source_image_names
            )
        )

    @property
    def runtime_source_image_names(self) -> tuple[str, ...]:
        """Return the complete alias axis for projectable runtime planes."""

        self._ensure_identity_cache()
        names = tuple(plane.source_image_name for plane in self._runtime_planes)
        if not names or any(name is None for name in names):
            return ()
        return tuple(name for name in names if name is not None)

    @property
    def contributor_count(self) -> int:
        return len(self.contributors)

    @property
    def plane_count_sources(self) -> tuple[int, ...]:
        path_count = len(self.paths)
        component_metadata_count = len(self.component_metadata)
        return tuple(
            count for count in (path_count, component_metadata_count) if count > 0
        )

    @property
    def has_values(self) -> bool:
        return bool(self.planes)

    @property
    def identity(self) -> tuple[SourceImageProvenancePlaneIdentity, ...]:
        self._ensure_identity_cache()
        return self._identity

    def _ensure_identity_cache(self) -> None:
        """Populate cached identity fields for older unpickled instances."""
        if hasattr(self, "_identity"):
            return
        self._paths = tuple(plane.path for plane in self.planes)
        self._component_metadata = tuple(
            plane.component_metadata for plane in self.planes
        )
        self._identity = tuple(plane.identity for plane in self.planes)
        self._runtime_planes = tuple(
            plane
            for plane in self.planes
            if isinstance(plane, RuntimeSourceImageProvenancePlane)
        )

    def _plane_values(
        self,
        select: Callable[
            [SourceImageProvenancePlane], SourceImageProvenancePlaneValueT
        ],
    ) -> tuple[SourceImageProvenancePlaneValueT, ...]:
        return tuple(select(plane) for plane in self.planes)

    def plane(self, index: int) -> SourceImageProvenancePlane:
        self._ensure_identity_cache()
        if 0 <= index < len(self._runtime_planes):
            return self._runtime_planes[index]
        return RuntimeSourceImageProvenancePlane()

    def select(self, indices: Sequence[int]) -> "SourceImageProvenancePlanes":
        """Return provenance planes selected by source-plane index."""
        return type(self)(tuple(self.plane(int(index)) for index in indices))

    def as_contributors(
        self,
        source_image_names: Sequence[str] = (),
    ) -> "SourceImageProvenancePlanes":
        """Reclassify removed runtime planes as non-projectable contributors."""
        names = tuple(str(name) for name in source_image_names)
        contributors: list[SourceImageProvenanceContributor] = []
        runtime_index = 0
        for plane in self.planes:
            if isinstance(plane, SourceImageProvenanceContributor):
                contributors.append(plane)
                continue
            if plane.contributors:
                contributors.extend(plane.contributors)
            else:
                source_image_name = (
                    names[runtime_index]
                    if runtime_index < len(names)
                    else plane.source_image_name
                )
                contributors.append(
                    SourceImageProvenanceContributor(
                        plane.source_identity,
                        source_image_name=source_image_name,
                    )
                )
            runtime_index += 1
        unique_contributors: list[SourceImageProvenanceContributor] = []
        named_addresses: dict[
            tuple[str, str | None], list[SourceImageProvenanceContributor]
        ] = {}
        for contributor in contributors:
            # A derived image and its original can name the same source at this
            # runtime slice. Removed axes represent source identities, not the
            # number of routes through which those sources contributed pixels.
            # Read current addresses; the identity snapshot can predate edits.
            if (
                contributor.source_image_name is not None
                and contributor.source_identity.addressable
            ):
                address = (contributor.source_image_name, contributor.path)
                same_address = named_addresses.setdefault(address, [])
                if any(
                    existing.component_metadata == contributor.component_metadata
                    for existing in same_address
                ):
                    continue
                same_address.append(contributor)
            unique_contributors.append(contributor)
        return type(self)(tuple(unique_contributors))

    def with_missing_from(
        self,
        fallback: "SourceImageProvenancePlanes",
    ) -> "SourceImageProvenancePlanes":
        if not self.planes:
            return fallback
        if not fallback.planes or len(self.planes) != len(fallback.planes):
            return self
        return type(self)(
            tuple(
                plane.with_missing_from(fallback_plane)
                for plane, fallback_plane in zip(self.planes, fallback.planes)
            )
        )


class SourceImageProvenance:
    """Source-image identity carried by image and object-label payloads."""

    __slots__ = (
        "source_identity",
        "source_image_provenance_planes",
        "source_image_names",
        "_equality_identity",
    )

    def __init__(
        self,
        source_path: str | None = None,
        source_component_metadata: SourceComponentMetadata | None = None,
        source_image_provenance_planes: SourceImageProvenancePlanes | None = None,
        source_image_names: tuple[str, ...] = (),
    ) -> None:
        self.source_identity = SourceImageIdentity(
            source_path, source_component_metadata
        )
        self.source_image_provenance_planes = (
            source_image_provenance_planes or SourceImageProvenancePlanes()
        )
        self.source_image_names = tuple(str(name) for name in source_image_names)
        self._equality_identity = (
            self.source_identity.identity,
            self.source_image_provenance_planes.identity,
            self.source_image_names,
        )

    def as_runtime_plane(self) -> RuntimeSourceImageProvenancePlane:
        """Compose one scalar source, retaining its non-projectable contributors."""
        names = self.source_image_names
        contributors = self.source_image_provenance_planes.as_contributors(names).planes
        if len(names) > 1:
            raise ValueError(
                "Composed image payload provenance permits at most one "
                f"source alias per scalar plane, got {names!r}."
            )
        return RuntimeSourceImageProvenancePlane(
            SourceImageIdentity(self.source_path, self.source_component_metadata),
            contributors,
            names[0] if names else None,
        )

    @classmethod
    def stack(
        cls,
        sources: Sequence["SourceImageProvenance"],
        *,
        scalar_sources: Sequence["SourceImageProvenance"] | None = None,
        preserve_single_topology: bool = True,
    ) -> Self:
        """Compose ordered runtime sources with their common scalar coordinates."""
        return cls._compose(
            tuple(sources),
            scalar_sources,
            preserve_single_topology=preserve_single_topology,
            bundle=False,
        )

    @classmethod
    def bundle(
        cls,
        sources: Sequence["SourceImageProvenance"],
        *,
        scalar_sources: Sequence["SourceImageProvenance"] | None = None,
        preserve_single_topology: bool = False,
    ) -> Self:
        """Compose same-slice sources, retaining nonconflicting partial coordinates."""
        return cls._compose(
            tuple(sources),
            scalar_sources,
            preserve_single_topology=preserve_single_topology,
            bundle=True,
        )

    @staticmethod
    def bundle_component_metadata(
        sources: Sequence["SourceImageProvenance"],
        *,
        scalar_sources: Sequence["SourceImageProvenance"] | None = None,
    ) -> SourceComponentMetadata | None:
        metadata = tuple(
            SourceMetadataFields.composition_snapshot(fields)
            for fields in SourceImageProvenance._composition_component_metadata(
                sources, scalar_sources
            )
            if fields is not None
        )
        common: dict[str, SourceMetadataValue] = {}
        for name in set().union(*(fields.keys() for fields in metadata)):
            values = tuple(fields[name] for fields in metadata if name in fields)
            if values and all(value == values[0] for value in values):
                common[name] = values[0]
        if not common:
            return None
        owner = (
            metadata[0]
            if metadata
            and all(
                isinstance(fields, OwnedSourceMetadataFields) for fields in metadata
            )
            else {}
        )
        derived = SourceMetadataFields.derived_mapping(owner, common)
        return (
            derived
            if isinstance(derived, OwnedSourceMetadataFields)
            else MappingProxyType(derived)
        )

    @staticmethod
    def _composition_component_metadata(
        sources: Sequence["SourceImageProvenance"],
        scalar_sources: Sequence["SourceImageProvenance"] | None,
    ) -> tuple[SourceComponentMetadata | None, ...]:
        """Retain authored scalar coordinates before inheriting selected plane facts."""
        if scalar_sources is None:
            scalar_sources = sources
        return tuple(
            (
                scalar.source_component_metadata
                if scalar.source_component_metadata is not None
                else selected.source_component_metadata
            )
            for scalar, selected in zip(scalar_sources, sources, strict=True)
        )

    @classmethod
    def _compose(
        cls,
        sources: tuple["SourceImageProvenance", ...],
        scalar_sources: Sequence["SourceImageProvenance"] | None,
        *,
        preserve_single_topology: bool,
        bundle: bool,
    ) -> Self:
        if not sources:
            raise ValueError("Source provenance composition cannot be empty.")
        planes = (
            sources[0].source_image_provenance_planes
            if preserve_single_topology
            and len(sources) == 1
            and sources[0].source_plane_count > 1
            else SourceImageProvenancePlanes(
                tuple(source.as_runtime_plane() for source in sources)
            )
        )
        component_metadata = (
            cls.bundle_component_metadata(sources, scalar_sources=scalar_sources)
            if bundle
            else common_source_component_metadata(
                cls._composition_component_metadata(sources, scalar_sources)
            )
        )
        present_paths = tuple(
            source.source_path for source in sources if source.source_path is not None
        )
        return cls(
            source_path=common_source_path(present_paths),
            source_component_metadata=component_metadata,
            source_image_provenance_planes=planes,
            source_image_names=planes.runtime_source_image_names,
        )

    @classmethod
    def from_init_values(
        cls,
        values: SourceProvenanceInitValues,
    ) -> "SourceImageProvenance":
        return cls(*values)

    @classmethod
    def from_mapping(cls, values: Mapping[str, object]) -> "SourceImageProvenance":
        """Decode constructor-owned facts, retaining nominal contributor records."""
        parameters = signature(cls).parameters
        unknown = set(values) - set(parameters)
        if unknown:
            raise ValueError(f"Unknown source provenance fields: {sorted(unknown)!r}.")
        decoded = dict(values)
        plane_field = "source_image_provenance_planes"
        if plane_field in decoded:
            decoded[plane_field] = SourceImageProvenancePlanes.from_mapping(
                decoded[plane_field]
            )
        result = cls(**decoded)
        annotations = get_type_hints(cls.__init__)
        for name in parameters:
            validate_annotation_value(
                annotations[name], getattr(result, name), path=f"{cls.__name__}.{name}"
            )
        return result

    @property
    def source_path(self) -> str | None:
        return self.source_identity.path

    @property
    def source_component_metadata(self) -> SourceComponentMetadata | None:
        return self.source_identity.component_metadata

    @property
    def has_values(self) -> bool:
        return any(
            (
                self.source_identity.addressable,
                self.source_image_provenance_planes.has_values,
                bool(self.source_image_names),
            )
        )

    @property
    def source_plane_count(self) -> int:
        return self.source_image_provenance_planes.count

    @property
    def represented_source_image_names(self) -> tuple[str, ...]:
        """Return every source alias carried by runtime planes or contributors."""

        return tuple(
            dict.fromkeys(
                (
                    *self.source_image_names,
                    *self.source_image_provenance_planes.represented_source_image_names,
                )
            )
        )

    @property
    def represented_source_identities(self) -> tuple[SourceImageIdentity, ...]:
        """Return exact addressable leaf identities represented by this payload."""

        identities: list[SourceImageIdentity] = []
        for plane in self.source_image_provenance_planes.planes:
            represented = (
                tuple(
                    contributor.source_identity.with_missing_from(plane.source_identity)
                    for contributor in plane.contributors
                )
                if plane.contributors
                else (plane.source_identity,)
            )
            for identity in represented:
                resolved = identity.with_missing_from(self.source_identity)
                if resolved.addressable:
                    identities.append(resolved)
        if not identities and self.source_identity.addressable:
            identities.append(self.source_identity)

        unique: list[SourceImageIdentity] = []
        seen: set[SourceProvenanceIdentity] = set()
        for identity in identities:
            if identity.identity in seen:
                continue
            seen.add(identity.identity)
            unique.append(identity)
        return tuple(unique)

    @property
    def plane_count_sources(self) -> tuple[int, ...]:
        return self.source_image_provenance_planes.plane_count_sources

    @property
    def addressable(self) -> bool:
        return self.source_identity.addressable

    @property
    def scalar_source_identity(self) -> SourceImageIdentity:
        """Return scalar source identity without collapsing multi-plane provenance."""
        if self.source_image_provenance_planes.count == 1:
            return self.source_identity.with_missing_from(
                self.source_image_provenance_planes.plane(0).source_identity
            )
        return self.source_identity

    def required_scalar_components(
        self, component_order: Iterable[str]
    ) -> tuple[str, ...]:
        """Exclude only coordinates proven reduced into pixel contributors.

        Contributors do not own a projectable runtime axis. A component that
        varies across their complete source addresses therefore has no scalar
        address on the derived image. Absent or incomplete contributor evidence
        cannot exempt an acquired plane from its required coordinates.
        """
        contributors = self.source_image_provenance_planes.contributors
        scalar_components = SourceMetadataFields.component_domains(
            self.scalar_source_identity.component_metadata or {}
        )
        contributor_components = tuple(
            SourceMetadataFields.component_domains(contributor.component_metadata or {})
            for contributor in contributors
        )
        reduced = set()
        for component in AxisFamily.active().axes:
            if component in scalar_components:
                continue
            if len(contributor_components) < 2 or not all(
                len(values.get(component, ())) == 1 for values in contributor_components
            ):
                continue
            values = frozenset(
                value for values in contributor_components for value in values[component]
            )
            if len(values) > 1:
                reduced.add(component.name)
        return tuple(component for component in component_order if component not in reduced)

    def image_set_identities(
        self,
        policy: SourceImageSetIdentityPolicy,
    ) -> frozenset[SourceImageSetIdentity]:
        """Return the image-set identity represented by scalar provenance."""
        return self.source_identity.image_set_identities(policy)

    def image_set_axis(
        self,
        policy: SourceImageSetIdentityPolicy,
    ) -> tuple[frozenset[SourceImageSetIdentity], ...]:
        """Return distinct image-set identities in runtime plane order."""
        identities = self.image_set_plane_identities(policy)
        if not identities:
            identities = (self.image_set_identities(policy),)
        return tuple(dict.fromkeys(identity for identity in identities if identity))

    def image_set_plane_identities(
        self,
        policy: SourceImageSetIdentityPolicy,
    ) -> tuple[frozenset[SourceImageSetIdentity], ...]:
        """Return one image-set identity entry for every runtime source plane."""
        return tuple(
            self.source_image_provenance_planes.plane(
                index
            ).source_identity.with_missing_from(
                self.source_identity
            ).image_set_identities(policy)
            for index in range(self.source_plane_count)
        )

    def component_metadata_for_plane(
        self, plane_index: int
    ) -> SourceComponentMetadata | None:
        """Read current plane coordinates with their scalar source fallback."""
        if not self.source_plane_count:
            return self.source_component_metadata
        return self.source_image_provenance_planes.plane(
            plane_index
        ).source_identity.component_metadata_with_missing_from(self.source_identity)

    def for_source_plane(self, plane_index: int) -> "SourceImageProvenance":
        if self.source_plane_count == 0:
            return type(self)(
                source_path=self.source_identity.path,
                source_component_metadata=self.source_identity.component_metadata,
                source_image_provenance_planes=self.source_image_provenance_planes,
                source_image_names=self.source_image_names_for_planes((plane_index,)),
            )
        provenance_plane = self.source_image_provenance_planes.plane(plane_index)
        source_identity = provenance_plane.source_identity.with_missing_from(
            self.source_identity
        )
        return type(self)(
            source_path=source_identity.path,
            source_component_metadata=source_identity.component_metadata,
            source_image_provenance_planes=SourceImageProvenancePlanes(
                provenance_plane.contributors
            ),
            source_image_names=self.source_image_names_for_plane(plane_index),
        )

    def for_source_planes(
        self, plane_indices: Sequence[int]
    ) -> "SourceImageProvenance":
        """Return provenance represented by a grouped set of source planes."""
        normalized_indices = tuple(int(index) for index in plane_indices)
        if self.source_plane_count == 0:
            return type(self)(
                source_path=self.source_identity.path,
                source_component_metadata=self.source_identity.component_metadata,
                source_image_provenance_planes=self.source_image_provenance_planes,
                source_image_names=self.source_image_names_for_planes(
                    normalized_indices
                ),
            )
        if len(normalized_indices) == 1:
            return self.for_source_plane(normalized_indices[0])
        return type(self)(
            source_path=self.source_identity.path,
            source_component_metadata=self.source_identity.component_metadata,
            source_image_provenance_planes=(
                self.source_image_provenance_planes.select(
                    normalized_indices
                ).with_missing_from(
                    SourceImageProvenancePlanes.from_components(
                        paths=(self.source_identity.path,) * len(normalized_indices),
                        component_metadata=(self.source_identity.component_metadata,)
                        * len(normalized_indices),
                    )
                )
            ),
            source_image_names=self.source_image_names_for_planes(normalized_indices),
        )

    def for_source_image(self, source_image_name: str) -> "SourceImageProvenance":
        """Project one exact named source while preserving its runtime plane axis."""

        normalized_name = str(source_image_name).strip()
        if not normalized_name:
            raise ValueError("Source-image provenance projection requires a name.")
        plane_selection = self.source_plane_selection(normalized_name)
        if plane_selection is None:
            raise ValueError(
                f"Source provenance does not represent {normalized_name!r}; "
                f"available names are {self.represented_source_image_names!r}."
            )
        if not plane_selection:
            contributors = tuple(
                contributor
                for contributor in self.source_image_provenance_planes.contributors
                if contributor.source_image_name == normalized_name
            )
            if normalized_name in self.source_image_names:
                source_identity = self.source_identity
            elif len(contributors) == 1:
                source_identity = contributors[0].source_identity
            else:
                raise ValueError(
                    "Scalar source provenance must declare exactly one identity for "
                    f"source image {normalized_name!r}; found {len(contributors)}."
                )
            return type(self)(
                source_path=source_identity.path,
                source_component_metadata=source_identity.component_metadata,
                source_image_names=(normalized_name,),
            )

        declared_names = self.source_image_names
        projected_planes: list[RuntimeSourceImageProvenancePlane] = []
        for plane_index in plane_selection:
            plane = self.source_image_provenance_planes.plane(plane_index)
            declared_name = (
                declared_names[0]
                if len(declared_names) == 1
                else (
                    declared_names[plane_index]
                    if len(declared_names) == self.source_plane_count
                    else None
                )
            )
            source_identity = (
                plane.source_identity
                if declared_name == normalized_name
                else plane.source_identity_for_name(normalized_name)
            )
            projected_planes.append(
                RuntimeSourceImageProvenancePlane(
                    source_identity,
                    source_image_name=normalized_name,
                )
            )
        return type(self)(
            source_image_provenance_planes=SourceImageProvenancePlanes(
                tuple(projected_planes)
            ),
            source_image_names=(normalized_name,),
        ).with_common_scalar_identity_from_planes()

    def varying_plane_component_values(
        self,
        components: Sequence[type[Axis]],
    ) -> dict[str, tuple[SourceMetadataScalar, ...]]:
        """Return exact component values that vary across declared source planes."""
        if not components or self.source_plane_count <= 1:
            return {}
        metadata_by_plane = tuple(
            self.component_metadata_for_plane(index) or {}
            for index in range(self.source_plane_count)
        )
        values_by_component: dict[str, tuple[SourceMetadataScalar, ...]] = {}
        for component in components:
            values = tuple(
                source_component_metadata_raw_value(
                    metadata,
                    component,
                )
                for metadata in metadata_by_plane
            )
            if any(value is None for value in values):
                continue
            if len(frozenset(values)) > 1:
                values_by_component[component.name] = values
        return values_by_component

    def require_common_component_values(
        self,
        components: Sequence[type[Axis]],
    ) -> tuple[tuple[type[Axis], str], ...]:
        """Return fixed component values shared by every represented source plane."""

        if not components:
            return ()
        metadata_by_plane = (
            tuple(
                self.component_metadata_for_plane(index) or {}
                for index in range(self.source_plane_count)
            )
            if self.source_plane_count
            else (self.source_component_metadata or {},)
        )
        values: list[tuple[type[Axis], str]] = []
        for component in components:
            metadata_values = tuple(
                source_component_metadata_value(
                    metadata,
                    component,
                )
                for metadata in metadata_by_plane
            )
            if any(value is None for value in metadata_values):
                raise ValueError(
                    "Source provenance does not declare component "
                    f"{component.name!r} on every represented plane."
                )
            unique_values = tuple(dict.fromkeys(metadata_values))
            if len(unique_values) != 1:
                raise ValueError(
                    f"Source provenance component {component.name!r} is not fixed: "
                    f"{unique_values!r}."
                )
            values.append((component, unique_values[0]))
        return tuple(values)

    def source_image_names_for_plane(self, plane_index: int) -> tuple[str, ...]:
        """Return source-image aliases represented by a selected provenance plane."""
        plane_name = self.source_image_provenance_planes.plane(
            plane_index
        ).source_image_name
        if plane_name is not None:
            return (plane_name,)
        if len(self.source_image_names) <= plane_index:
            return self.source_image_names
        return (self.source_image_names[plane_index],)

    def source_image_names_for_planes(
        self,
        plane_indices: Sequence[int],
    ) -> tuple[str, ...]:
        """Return aliases represented by selected provenance planes."""
        normalized_indices = tuple(int(index) for index in plane_indices)
        if not normalized_indices:
            return ()
        if len(self.source_image_names) <= max(normalized_indices):
            return self.source_image_names
        return tuple(self.source_image_names[index] for index in normalized_indices)

    def source_plane_selection(
        self,
        source_image_name: str,
    ) -> tuple[int, ...] | None:
        """Return planes representing one declared source image name.

        An empty tuple denotes a matching scalar provenance value. ``None``
        denotes that this provenance does not represent the requested name.
        """

        if self.source_plane_count == 0:
            return (
                () if source_image_name in self.represented_source_image_names else None
            )
        if self.source_image_names:
            if len(self.source_image_names) == 1:
                if source_image_name == self.source_image_names[0]:
                    return tuple(range(self.source_plane_count))
            elif len(self.source_image_names) == self.source_plane_count:
                declared_selection = tuple(
                    plane_index
                    for plane_index, declared_name in enumerate(self.source_image_names)
                    if source_image_name == declared_name
                )
                if declared_selection:
                    return declared_selection
            else:
                raise ValueError(
                    "Source-image names must contain one shared name or exactly "
                    "one name per runtime plane: "
                    f"{len(self.source_image_names)} name(s) for "
                    f"{self.source_plane_count} plane(s)."
                )
        matching_planes = tuple(
            plane_index
            for plane_index in range(self.source_plane_count)
            if source_image_name
            in self.source_image_provenance_planes.plane(
                plane_index
            ).represented_source_image_names
        )
        return matching_planes or None

    def source_alias_plane_index(
        self,
        source_aliases: Sequence[str],
        axis_size: int,
    ) -> int | None:
        """Return the one plane selected by one exact source alias."""

        aliases = tuple(dict.fromkeys(str(alias) for alias in source_aliases))
        if len(aliases) != 1:
            return None
        selection = self.source_plane_selection(aliases[0])
        if selection is None or len(selection) != 1:
            return None
        plane_index = selection[0]
        return plane_index if plane_index < axis_size else None

    def identity(self) -> SourceProvenanceIdentity:
        return self.source_identity.identity

    @property
    def equality_identity(self) -> SourceImageProvenanceIdentity:
        """Return every semantic field that defines this provenance value."""
        if not hasattr(self, "_equality_identity"):
            self._equality_identity = (
                self.source_identity.identity,
                self.source_image_provenance_planes.identity,
                self.source_image_names,
            )
        return self._equality_identity

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SourceImageProvenance):
            return NotImplemented
        return self.equality_identity == other.equality_identity

    def with_missing_from(self, fallback: "SourceImageProvenance") -> Self:
        source_identity = self.source_identity.with_missing_from(
            fallback.source_identity
        )
        return type(self)(
            source_path=source_identity.path,
            source_component_metadata=source_identity.component_metadata,
            source_image_provenance_planes=(
                self.source_image_provenance_planes.with_missing_from(
                    fallback.source_image_provenance_planes
                )
            ),
            source_image_names=(
                self.source_image_names
                if self.source_image_names
                else fallback.source_image_names
            ),
        )

    def with_source_path(self, value: str | None) -> Self:
        """Return provenance with only the scalar source path replaced."""
        return type(self)(
            source_path=value,
            source_component_metadata=self.source_identity.component_metadata,
            source_image_provenance_planes=self.source_image_provenance_planes,
            source_image_names=self.source_image_names,
        )

    def with_source_component_metadata(
        self,
        value: SourceComponentMetadata | None,
    ) -> Self:
        """Return provenance with only the scalar component metadata replaced."""
        return type(self)(
            source_path=self.source_identity.path,
            source_component_metadata=value,
            source_image_provenance_planes=self.source_image_provenance_planes,
            source_image_names=self.source_image_names,
        )

    def with_source_image_provenance_planes(
        self,
        value: SourceImageProvenancePlanes,
    ) -> Self:
        """Return provenance with only the per-plane identities replaced."""
        return type(self)(
            source_path=self.source_identity.path,
            source_component_metadata=self.source_identity.component_metadata,
            source_image_provenance_planes=value,
            source_image_names=self.source_image_names,
        )

    def with_source_image_names(self, value: tuple[str, ...]) -> Self:
        """Return provenance with only source-image aliases replaced."""
        return type(self)(
            source_path=self.source_identity.path,
            source_component_metadata=self.source_identity.component_metadata,
            source_image_provenance_planes=self.source_image_provenance_planes,
            source_image_names=value,
        )

    def with_derived_source_image_names(self, value: tuple[str, ...]) -> Self:
        """Name a derived image without discarding its scalar source names."""

        names = tuple(str(name) for name in value)
        provenance_planes = self.source_image_provenance_planes
        if self.source_plane_count and names:
            if len(names) not in (1, self.source_plane_count):
                raise ValueError(
                    "Derived image names must contain one shared name or exactly "
                    "one name per runtime plane: "
                    f"{len(names)} name(s) for {self.source_plane_count} plane(s)."
                )
            plane_names = names * self.source_plane_count if len(names) == 1 else names
            renamed_planes: list[SourceImageProvenancePlane] = []
            runtime_index = 0
            for plane in provenance_planes.planes:
                if isinstance(plane, SourceImageProvenanceContributor):
                    renamed_planes.append(plane)
                    continue
                contributors = plane.contributors
                contributor_names = {
                    contributor.source_image_name for contributor in contributors
                }
                prior_plane_names = self.source_image_names_for_plane(runtime_index)
                for prior_plane_name in prior_plane_names:
                    if (
                        prior_plane_name == plane_names[runtime_index]
                        or prior_plane_name in contributor_names
                    ):
                        continue
                    contributors = (
                        *contributors,
                        SourceImageProvenanceContributor(
                            plane.source_identity,
                            source_image_name=prior_plane_name,
                        ),
                    )
                    contributor_names.add(prior_plane_name)
                renamed_planes.append(
                    RuntimeSourceImageProvenancePlane(
                        plane.source_identity,
                        contributors,
                        plane_names[runtime_index],
                    )
                )
                runtime_index += 1
            provenance_planes = type(provenance_planes)(tuple(renamed_planes))
        if self.source_plane_count == 0:
            represented_names = frozenset(
                provenance_planes.represented_source_image_names
            )
            retained_names = tuple(
                name
                for name in self.source_image_names
                if name not in names and name not in represented_names
            )
            if retained_names:
                provenance_planes = type(provenance_planes)(
                    (
                        *provenance_planes.planes,
                        *(
                            SourceImageProvenanceContributor(
                                self.source_identity,
                                source_image_name=name,
                            )
                            for name in retained_names
                        ),
                    )
                )
        return type(self)(
            source_path=self.source_identity.path,
            source_component_metadata=self.source_identity.component_metadata,
            source_image_provenance_planes=provenance_planes,
            source_image_names=names,
        )

    def with_runtime_planes_as_contributors(self) -> Self:
        """Reclassify a removed runtime axis without losing source identities."""
        if self.source_plane_count == 0:
            return self
        contributor_planes = self.source_image_provenance_planes.as_contributors(
            self.source_image_names
        )
        if not contributor_planes.planes and (
            self.source_identity.addressable or len(self.source_image_names) == 1
        ):
            contributor_planes = SourceImageProvenancePlanes(
                (
                    SourceImageProvenanceContributor(
                        self.source_identity,
                        source_image_name=(
                            self.source_image_names[0]
                            if self.source_image_names
                            else None
                        ),
                    ),
                )
            )
        return type(self)(
            source_path=self.source_identity.path,
            source_component_metadata=self.source_identity.component_metadata,
            source_image_provenance_planes=contributor_planes,
            source_image_names=(),
        )

    def with_common_scalar_identity_from_planes(self) -> Self:
        """Return provenance whose scalar identity is common to all planes."""
        if not self.source_image_provenance_planes.has_values:
            return self
        return type(self)(
            source_path=common_source_path(self.source_image_provenance_planes.paths),
            source_component_metadata=common_source_component_metadata(
                self.source_image_provenance_planes.component_metadata
            ),
            source_image_provenance_planes=self.source_image_provenance_planes,
            source_image_names=self.source_image_names,
        )

    @property
    def source_component_identity(self) -> tuple[tuple[str, str], ...] | None:
        return self.source_identity.identity[1]


@dataclass(frozen=True, slots=True)
class SourcePlaneIndexedMetadata:
    """Source metadata for one indexed plane inside a single source image."""

    scalar_metadata: SourceComponentMetadata
    scalar_plane_index: int
    source_plane_count: int

    @staticmethod
    def projected_component() -> type[Axis]:
        """Return the stack axis that indexed source-plane metadata represents."""
        return AxisFamily.active().one(StackAxis)

    @classmethod
    def from_metadata(
        cls,
        metadata: SourceComponentMetadata,
        *,
        expected_plane_count: int,
    ) -> "SourcePlaneIndexedMetadata | None":
        index_value = source_metadata_value(metadata, SOURCE_PLANE_INDEX_FIELD)
        count_value = source_metadata_value(metadata, SOURCE_PLANE_COUNT_FIELD)
        if index_value is None and count_value is None:
            return None
        if index_value is None or count_value is None:
            raise ValueError(
                "Source-plane metadata must carry both "
                f"{SOURCE_PLANE_INDEX_FIELD!r} and {SOURCE_PLANE_COUNT_FIELD!r}."
            )
        indexed_metadata = cls(
            scalar_metadata=metadata,
            scalar_plane_index=cls.parse_source_plane_value(
                index_value,
                field_name=SOURCE_PLANE_INDEX_FIELD,
            ),
            source_plane_count=cls.parse_source_plane_value(
                count_value,
                field_name=SOURCE_PLANE_COUNT_FIELD,
            ),
        )
        if indexed_metadata.source_plane_count != expected_plane_count:
            raise ValueError(
                "Declared source-plane count conflicts with the owning runtime "
                f"axis: {indexed_metadata.source_plane_count} != "
                f"{expected_plane_count}."
            )
        indexed_metadata.validate_scalar_plane_index()
        return indexed_metadata

    @classmethod
    def from_declared_source_metadata(
        cls,
        metadata: SourceComponentMetadata,
    ) -> "SourcePlaneIndexedMetadata | None":
        """Return exact source-plane semantics declared by source metadata."""
        index_value = source_metadata_value(metadata, SOURCE_PLANE_INDEX_FIELD)
        count_value = source_metadata_value(metadata, SOURCE_PLANE_COUNT_FIELD)
        if index_value is None and count_value is None:
            return None
        if index_value is None or count_value is None:
            raise ValueError(
                "Source-plane metadata must carry both "
                f"{SOURCE_PLANE_INDEX_FIELD!r} and {SOURCE_PLANE_COUNT_FIELD!r}."
            )
        indexed_metadata = cls(
            scalar_metadata=metadata,
            scalar_plane_index=cls.parse_source_plane_value(
                index_value,
                field_name=SOURCE_PLANE_INDEX_FIELD,
            ),
            source_plane_count=cls.parse_source_plane_value(
                count_value,
                field_name=SOURCE_PLANE_COUNT_FIELD,
            ),
        )
        indexed_metadata.validate_scalar_plane_index()
        return indexed_metadata

    @classmethod
    def from_scalar_origin(
        cls,
        metadata: SourceComponentMetadata,
        *,
        source_plane_count: int,
    ) -> "SourcePlaneIndexedMetadata | None":
        index_value = source_metadata_value(metadata, SOURCE_PLANE_INDEX_FIELD)
        count_value = source_metadata_value(metadata, SOURCE_PLANE_COUNT_FIELD)
        if index_value is None and count_value is None:
            return None
        if (index_value is None) != (count_value is None):
            raise ValueError(
                "Source-plane metadata must carry both "
                f"{SOURCE_PLANE_INDEX_FIELD!r} and {SOURCE_PLANE_COUNT_FIELD!r}."
            )
        scalar_plane_index = (
            0
            if index_value is None
            else cls.parse_source_plane_value(
                index_value,
                field_name=SOURCE_PLANE_INDEX_FIELD,
            )
        )
        declared_count = (
            source_plane_count
            if count_value is None
            else cls.parse_source_plane_value(
                count_value,
                field_name=SOURCE_PLANE_COUNT_FIELD,
            )
        )
        if declared_count != source_plane_count:
            raise ValueError(
                "Volumetric source metadata plane count disagrees with image "
                f"shape: {declared_count} != {source_plane_count}."
            )
        indexed_metadata = cls(
            scalar_metadata=metadata,
            scalar_plane_index=scalar_plane_index,
            source_plane_count=source_plane_count,
        )
        indexed_metadata.validate_scalar_plane_index()
        return indexed_metadata

    @classmethod
    def from_declared_runtime_stack_origin(
        cls,
        metadata: SourceComponentMetadata,
        *,
        source_plane_count: int,
    ) -> "SourcePlaneIndexedMetadata | None":
        indexed_metadata = cls.from_scalar_origin(
            metadata,
            source_plane_count=source_plane_count,
        )
        if indexed_metadata is not None:
            return indexed_metadata
        scalar_axis_value = source_component_metadata_value(
            metadata,
            cls.projected_component(),
        )
        if scalar_axis_value is None:
            return None
        indexed_metadata = cls(
            scalar_metadata=metadata,
            scalar_plane_index=0,
            source_plane_count=source_plane_count,
        )
        indexed_metadata.validate_scalar_plane_index()
        return indexed_metadata

    @staticmethod
    def parse_source_plane_value(value: str, *, field_name: str) -> int:
        try:
            return int(value)
        except ValueError as exc:
            raise ValueError(
                f"Source-plane metadata field {field_name!r} must be numeric, "
                f"got {value!r}."
            ) from exc

    def validate_scalar_plane_index(self) -> None:
        if not 0 <= self.scalar_plane_index < self.source_plane_count:
            raise ValueError(
                "Source-plane metadata index is outside the declared plane "
                f"domain: {self.scalar_plane_index} for "
                f"{self.source_plane_count} planes."
            )

    def component_metadata(self) -> tuple[SourceComponentMetadata, ...]:
        return tuple(
            self.component_metadata_for_plane(plane_index)
            for plane_index in range(self.source_plane_count)
        )

    def component_metadata_for_plane(
        self,
        plane_index: int,
    ) -> SourceComponentMetadata:
        metadata = SourceMetadataFields.with_fields(
            SourceMetadataFields.composition_snapshot(self.scalar_metadata),
            {
                SOURCE_PLANE_INDEX_FIELD: str(plane_index),
                SOURCE_PLANE_COUNT_FIELD: str(self.source_plane_count),
            },
            components=(
                (self.projected_component(), self.z_index_for_plane(plane_index)),
            ),
        )
        return SourceMetadataFields.readonly_snapshot(metadata)

    def z_index_for_plane(self, plane_index: int) -> int:
        scalar_z_index = source_component_metadata_value(
            self.scalar_metadata,
            self.projected_component(),
        )
        if scalar_z_index is None:
            return plane_index + 1
        try:
            first_z_index = int(scalar_z_index) - self.scalar_plane_index
        except ValueError as exc:
            raise ValueError(
                "Source-plane metadata z_index must be numeric when expanding "
                f"indexed plane provenance, got {scalar_z_index!r}."
            ) from exc
        return first_z_index + plane_index

    def common_component_metadata(self) -> SourceComponentMetadata | None:
        return common_source_component_metadata(self.component_metadata())


@dataclass(frozen=True, slots=True)
class SourcePlaneIndexedProvenanceExpansion:
    """Expand scalar indexed source metadata into per-plane source provenance."""

    provenance: SourceImageProvenance
    expected_plane_count: int | None

    def expanded(self) -> SourceImageProvenance:
        if self.provenance.source_image_provenance_planes.has_values:
            return self.provenance
        metadata = self.provenance.source_component_metadata
        if metadata is None:
            return self.provenance
        indexed_metadata = (
            SourcePlaneIndexedMetadata.from_declared_source_metadata(metadata)
            if self.expected_plane_count is None
            else SourcePlaneIndexedMetadata.from_metadata(
                metadata,
                expected_plane_count=self.expected_plane_count,
            )
        )
        if indexed_metadata is None:
            return self.provenance
        plane_count = indexed_metadata.source_plane_count
        return SourceImageProvenance(
            source_path=self.provenance.source_path,
            source_component_metadata=indexed_metadata.common_component_metadata(),
            source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
                paths=(self.provenance.source_path,) * plane_count,
                component_metadata=indexed_metadata.component_metadata(),
            ),
            source_image_names=self.provenance.source_image_names,
        )


def common_source_component_metadata(
    metadata_by_plane: Sequence[SourceComponentMetadata | None],
) -> SourceComponentMetadata | None:
    """Return source metadata values shared by every source plane."""
    consensus = source_component_metadata_consensus(metadata_by_plane)
    if consensus is None:
        return None
    common_metadata = {
        key: value for key, value in consensus.items() if value is not None
    }
    if not common_metadata:
        return None
    return SourceMetadataFields.readonly_snapshot(
        SourceMetadataFields.derived_mapping(consensus, common_metadata)
    )


def source_component_metadata_consensus(
    metadata_by_plane: Sequence[SourceComponentMetadata | None],
) -> SourceComponentMetadata | None:
    """Return every metadata field, nulling values that differ between planes."""

    metadata_values = tuple(
        SourceMetadataFields.composition_snapshot(metadata)
        for metadata in metadata_by_plane
        if metadata is not None
    )
    if len(metadata_values) != len(metadata_by_plane):
        return None
    if not metadata_values:
        return None
    field_names = tuple(
        dict.fromkeys(
            field_name for metadata in metadata_values for field_name in metadata
        )
    )
    consensus: dict[str, SourceMetadataValue] = {}
    for field_name in field_names:
        present_values = tuple(
            metadata[field_name]
            for metadata in metadata_values
            if field_name in metadata
        )
        consensus[field_name] = (
            present_values[0]
            if len(present_values) == len(metadata_values)
            and all(value == present_values[0] for value in present_values)
            else None
        )
    owner = (
        metadata_values[0]
        if all(
            isinstance(metadata, OwnedSourceMetadataFields)
            for metadata in metadata_values
        )
        else {}
    )
    return SourceMetadataFields.readonly_snapshot(
        SourceMetadataFields.derived_mapping(owner, consensus)
    )


def common_source_path(paths: Sequence[str | None]) -> str | None:
    """Return the source path shared by every plane, if one exists."""
    path_values = tuple(path for path in paths if path is not None)
    if len(path_values) != len(paths) or not path_values:
        return None
    first = path_values[0]
    if all(path == first for path in path_values):
        return first
    return None


@dataclass(frozen=True, slots=True)
class SourceImageProvenanceRequirement(ABC, metaclass=AutoRegisterMeta):
    """Nominal source-provenance invariant with policy-selected failure behavior."""

    __registry_key__ = "requirement_name"
    __skip_if_no_key__ = True
    requirement_name: ClassVar[str | None] = None

    provenance: SourceImageProvenance
    label_name: str

    @property
    @abstractmethod
    def satisfied(self) -> bool:
        """Return whether this source-provenance invariant is satisfied."""

    @abstractmethod
    def error(self) -> ValueError:
        """Return the fail-loud error for an unsatisfied invariant."""

    def validate(self) -> None:
        SourceImageProvenanceRequirementPolicy.for_requirement(self).validate(self)


class SourceImageProvenanceRequirementPolicy(ABC, metaclass=AutoRegisterMeta):
    """Registered satisfied/unsatisfied handling for provenance requirements."""

    __registry_key__ = "satisfied"
    __skip_if_no_key__ = True
    satisfied: ClassVar[bool | None] = None

    @classmethod
    def for_requirement(
        cls,
        requirement: SourceImageProvenanceRequirement,
    ) -> "SourceImageProvenanceRequirementPolicy":
        return cls.__registry__[requirement.satisfied]()

    def validate(self, requirement: SourceImageProvenanceRequirement) -> None:
        """Validate one source-provenance requirement."""
        return None


class SatisfiedSourceImageProvenanceRequirementPolicy(
    SourceImageProvenanceRequirementPolicy
):
    """Accept source-provenance requirements that are already satisfied."""

    satisfied = True


class UnsatisfiedSourceImageProvenanceRequirementPolicy(
    SourceImageProvenanceRequirementPolicy
):
    """Raise the requirement-specific error for failed provenance invariants."""

    satisfied = False

    def validate(self, requirement: SourceImageProvenanceRequirement) -> None:
        raise requirement.error()


@dataclass(frozen=True, slots=True)
class SourceImageProvenancePlaneCountRequirement(SourceImageProvenanceRequirement):
    """Require per-plane source identities to match source-aligned label planes."""

    requirement_name = "plane_count"
    expected_count: int

    @property
    def satisfied(self) -> bool:
        return self.provenance.source_plane_count == self.expected_count

    def error(self) -> ValueError:
        return ValueError(
            f"Object-label artifact {self.label_name!r} has {self.expected_count} "
            "source-aligned label planes but "
            f"{self.provenance.source_plane_count} per-plane source identities "
            "after source-image contextualization."
        )


@dataclass(frozen=True, slots=True)
class SourceImageProvenanceAddressRequirement(SourceImageProvenanceRequirement):
    """Require one plane source identity to be addressable."""

    requirement_name = "address"
    plane_index: int

    @property
    def satisfied(self) -> bool:
        return self.provenance.addressable

    def error(self) -> ValueError:
        return ValueError(
            f"Object-label artifact {self.label_name!r} plane {self.plane_index} "
            "has neither source_path nor source_component_metadata after "
            "source-image contextualization."
        )


@dataclass(frozen=True, slots=True)
class SourceImageProvenanceAlias(Generic[SourceImageProvenanceAliasValueT]):
    """Descriptor for scalar aliases backed by the source-provenance carrier."""

    getter: Callable[[SourceImageProvenance], SourceImageProvenanceAliasValueT]
    setter: Callable[
        [SourceImageProvenance, SourceImageProvenanceAliasValueT],
        SourceImageProvenance,
    ]

    def __get__(
        self,
        instance: "SourceImageProvenanceFields | None",
        _owner: type["SourceImageProvenanceFields"],
    ) -> SourceImageProvenanceAliasValueT | Self:
        if instance is None:
            return self
        provenance = instance.source_provenance
        return self.getter(provenance)

    def __set__(
        self,
        instance: "SourceImageProvenanceFields",
        value: SourceImageProvenanceAliasValueT,
    ) -> None:
        instance.source_provenance = self.setter(instance.source_provenance, value)


@dataclass(kw_only=True)
class SourceImageProvenanceFields:
    """Source-image provenance fields shared by image and object-label carriers."""

    source_provenance: SourceImageProvenance = field(
        default_factory=SourceImageProvenance
    )
    source_path: InitVar[str | None] = None
    source_component_metadata: InitVar[SourceComponentMetadata | None] = None
    source_image_provenance_planes: InitVar[SourceImageProvenancePlanes | None] = None
    source_image_names: InitVar[tuple[str, ...]] = ()

    def absorb_explicit_source_provenance(
        self,
        values: SourceProvenanceInitValues,
    ) -> None:
        """Decode authored aliases once, leaving absent constructor facts absent."""
        if all(
            value is default
            for value, default in zip(
                values, SourceImageProvenance.__init__.__defaults__, strict=True
            )
        ):
            return
        explicit = SourceImageProvenance.from_init_values(values)
        if not explicit.has_values:
            return
        self.source_provenance = explicit.with_missing_from(self.source_provenance)

    def normalize_source_provenance_fields(self) -> None:
        self.source_provenance = SourceImageProvenance(
            self.source_provenance.source_path,
            self.source_provenance.source_component_metadata,
            self.source_provenance.source_image_provenance_planes,
            self.source_provenance.source_image_names,
        )

    def replace_fields(self, **changes: Any) -> Self:
        """Replace dataclass fields without replaying provenance alias values."""
        return replace(
            self,
            **{
                "source_path": None,
                "source_component_metadata": None,
                "source_image_provenance_planes": None,
                "source_image_names": (),
                **changes,
            },
        )


SourceImageProvenanceFields.source_path = SourceImageProvenanceAlias(
    lambda provenance: provenance.source_path,
    SourceImageProvenance.with_source_path,
)
SourceImageProvenanceFields.source_component_metadata = SourceImageProvenanceAlias(
    lambda provenance: provenance.source_component_metadata,
    SourceImageProvenance.with_source_component_metadata,
)
SourceImageProvenanceFields.source_image_provenance_planes = SourceImageProvenanceAlias(
    lambda provenance: provenance.source_image_provenance_planes,
    SourceImageProvenance.with_source_image_provenance_planes,
)
SourceImageProvenanceFields.source_image_names = SourceImageProvenanceAlias(
    lambda provenance: provenance.source_image_names,
    SourceImageProvenance.with_source_image_names,
)


@dataclass(frozen=True, slots=True)
class VariableComponentAxisProjection:
    """Project scalar source identity over variable component runtime planes."""

    axes: frozenset[str]

    @classmethod
    def empty(cls) -> "VariableComponentAxisProjection":
        return cls(frozenset())

    @classmethod
    def from_axes(
        cls,
        axes: Iterable[str],
    ) -> "VariableComponentAxisProjection":
        return cls(frozenset(axes))

    @property
    def is_empty(self) -> bool:
        return not self.axes

    def ordered_axes(self) -> tuple[str, ...]:
        component_order = AxisFamily.active().names()
        ordered_known = tuple(axis for axis in component_order if axis in self.axes)
        ordered_unknown = tuple(sorted(self.axes.difference(ordered_known)))
        return ordered_known + ordered_unknown

    def project_component_metadata(
        self,
        metadata: SourceComponentMetadata,
        plane_indices: Sequence[int],
    ) -> SourceComponentMetadata:
        axes = self.ordered_axes()
        if len(axes) != len(plane_indices):
            raise ValueError(
                "Variable component axis projection cannot map "
                f"{len(plane_indices)} runtime coordinate(s) onto declared axes "
                f"{axes!r}."
            )
        projected_metadata = metadata
        for axis, plane_index in zip(axes, plane_indices, strict=True):
            component = self.component_for_axis(axis)
            projected_metadata = with_source_component_metadata(
                projected_metadata,
                component,
                self.projected_axis_value(
                    projected_metadata,
                    component,
                    plane_index,
                ),
            )
        return projected_metadata

    def provenance_planes(
        self,
        *,
        source_path: str | None,
        source_component_metadata: SourceComponentMetadata | None,
        plane_count: int,
    ) -> SourceImageProvenancePlanes:
        if source_component_metadata is None:
            return SourceImageProvenancePlanes()
        if plane_count <= 0:
            return SourceImageProvenancePlanes()
        if len(self.ordered_axes()) != 1:
            return SourceImageProvenancePlanes()
        return SourceImageProvenancePlanes.from_components(
            paths=(source_path,) * plane_count,
            component_metadata=tuple(
                self.project_component_metadata(
                    source_component_metadata,
                    (plane_index,),
                )
                for plane_index in range(plane_count)
            ),
        )

    @staticmethod
    def component_for_axis(axis: str) -> type[Axis]:
        if axis not in AxisFamily.active().names():
            raise ValueError(
                "Variable component axis is not an OpenHCS component: " f"{axis!r}."
            )
        component = AxisFamily.active().named(axis)
        return component

    @staticmethod
    def projected_axis_value(
        metadata: SourceComponentMetadata,
        component: type[Axis],
        plane_index: int,
    ) -> int:
        current = source_component_metadata_raw_value(metadata, component)
        if current is None:
            raise ValueError(
                "Variable component axis projection requires scalar "
                f"{component.name!r} metadata."
            )
        if isinstance(current, bool):
            raise ValueError(
                "Variable component axis "
                f"{component.name!r} must be numeric, got bool."
            )
        try:
            base_value = int(current)
        except (TypeError, ValueError) as exc:
            raise ValueError(
                "Variable component axis "
                f"{component.name!r} must be numeric, got {current!r}."
            ) from exc
        return base_value + plane_index


@to_jsonable.register(SourceImageProvenance)
def _jsonable_source_provenance(value: SourceImageProvenance):
    """Project the public constructor declaration, not cached identity internals."""
    return {
        name: to_jsonable(getattr(value, name))
        for name in signature(SourceImageProvenance).parameters
    }


@to_jsonable.register(SourceImageProvenancePlanes)
def _jsonable_source_provenance_planes(value: SourceImageProvenancePlanes):
    return value.to_mapping()
