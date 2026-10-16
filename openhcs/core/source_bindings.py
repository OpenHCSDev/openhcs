"""Typed source-binding semantics for named step input views."""

from __future__ import annotations

import hashlib
import os
import re
import tempfile
import urllib.request
from abc import ABC, abstractmethod
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field, replace
from pathlib import Path, PureWindowsPath
from types import MappingProxyType
from typing import TYPE_CHECKING, Annotated, Any, ClassVar, Self, TypeVar
from urllib.parse import unquote, urlsplit

from metaclass_registry import AutoRegisterMeta

from openhcs.core.artifacts.plans import ArtifactSpecRef
from openhcs.core.artifacts.specs import ArtifactSpec, ArtifactSpecCollection
from openhcs.core.artifacts.kinds import ArtifactType, ImageArtifactType
from openhcs.core.component_set import ComponentSet
from polystore.formats import get_format_from_extension
from python_introspect import FieldLabel, RegisteredClassChoices
from openhcs.core.runtime_tabular_values import FieldSpec
from openhcs.core.source_metadata import (
    SourceMetadataFields,
    ResolvedSourceMetadataRecord,
    SourceMetadataMapping,
    SourceMetadataScalar,
    source_metadata_dict,
    source_metadata_scalar,
)
from openhcs.core.xdg_paths import get_openhcs_cache_dir
from openhcs.core.source_path_identity import source_path_posix, source_paths_equal
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.axis_boundaries import AxisChoices
from openhcs.core.axes import Axis, AxisFamily, GroupingDeclaration

if TYPE_CHECKING:
    from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
    from openhcs.core.runtime_array_values import RuntimeArrayData
    from openhcs.core.runtime_image_loading import ImagePayloadSourceMetadataContext
    from openhcs.core.runtime_image_values import ImagePayloadMetadata
    from openhcs.core.source_binding_selection import (
        SourceBoundAnchorPatternPolicy,
        SourcePatternResolutionContext,
    )
    from openhcs.core.source_image_provenance import SourceImageProvenance

SOURCE_ALIAS_PART_SEPARATOR = "__"
SOURCE_BINDING_ALIAS_METADATA_FIELD = "source_alias"
SourceBindingValue = TypeVar("SourceBindingValue")


class SourceBindingOrigin(ABC, metaclass=AutoRegisterMeta):
    """Where a named binding is resolved from."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[SourceBindingOrigin]]] = {}

    name: ClassVar[str | None] = None
    """Spelling in forms and on the wire."""


class FromStepInput(SourceBindingOrigin):
    """The planes the prior step hands this step."""

    name = "step_input"


class FromPipelineStart(SourceBindingOrigin):
    """The source planes as they were before the pipeline's first step."""

    name = "pipeline_start"


class SourceSetRole(ABC, metaclass=AutoRegisterMeta):
    """How one source binding takes part in source-set assembly."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[SourceSetRole]]] = {}

    name: ClassVar[str | None] = None
    """Spelling in forms and on the wire."""


class MatchedSource(SourceSetRole):
    """The alias determines which source sets exist and how many."""

    name = "matched"


class BroadcastSource(SourceSetRole):
    """The alias is appended to every assembled source set."""

    name = "broadcast"


class SourceProjectionRole(ABC, metaclass=AutoRegisterMeta):
    """How one source binding is represented in a materialized workspace."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[SourceProjectionRole]]] = {}

    name: ClassVar[str | None] = None
    """Spelling in forms and on the wire."""

    @classmethod
    def check_artifact_kind(cls, artifact_kind: type[ArtifactType]) -> None:
        """Reject an artifact kind this projection cannot carry."""


class PrimaryPlaneRole(SourceProjectionRole):
    """The source becomes a primary image plane of the step's stack."""

    name = "primary_plane"

    @classmethod
    def check_artifact_kind(cls, artifact_kind: type[ArtifactType]) -> None:
        if not issubclass(artifact_kind, ImageArtifactType):
            raise ValueError(
                "NamedSourceBinding primary-plane projections require an image "
                f"artifact kind, got {artifact_kind.__name__}."
            )


class SourceArtifactRole(SourceProjectionRole):
    """The source is handed to functions as a named artifact."""

    name = "source_artifact"


class MetadataSource(ABC, metaclass=AutoRegisterMeta):
    """Which text of a source path metadata extraction rules search."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[MetadataSource]]] = {}

    name: ClassVar[str | None] = None
    """Spelling in forms and on the wire."""

    @staticmethod
    @abstractmethod
    def texts(file_path: str) -> tuple[str, ...]:
        """The texts a rule's pattern is searched in, in order."""


class FromFileName(MetadataSource):
    name = "file_name"

    @staticmethod
    def texts(file_path: str) -> tuple[str, ...]:
        return (Path(file_path).name,)


class FromFolderName(MetadataSource):
    name = "folder_name"

    @staticmethod
    def texts(file_path: str) -> tuple[str, ...]:
        parent = Path(file_path).parent
        parent_path = source_path_posix(parent)
        if parent_path == parent.name:
            return (parent.name,)
        return (parent.name, parent_path)


class SourceFilterSubject(ABC, metaclass=AutoRegisterMeta):
    """Which part of a source path one filter clause inspects."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[SourceFilterSubject]]] = {}

    name: ClassVar[str | None] = None
    """Spelling in forms and on the wire."""

    @staticmethod
    @abstractmethod
    def text_of(file_path: str) -> str:
        """The text of ``file_path`` this subject names."""


class SourceFileName(SourceFilterSubject):
    name = "file"

    @staticmethod
    def text_of(file_path: str) -> str:
        return os.path.basename(file_path)


class SourceDirectory(SourceFilterSubject):
    name = "directory"

    @staticmethod
    def text_of(file_path: str) -> str:
        return os.path.dirname(file_path)


class SourceExtension(SourceFilterSubject):
    name = "extension"

    @staticmethod
    def text_of(file_path: str) -> str:
        return os.path.splitext(file_path)[1].lower()


class SourceFilterMatchType(ABC, metaclass=AutoRegisterMeta):
    """How one source filter clause matches a source path."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type[SourceFilterMatchType]]] = {}

    name: ClassVar[str | None] = None
    """Spelling in forms and on the wire."""

    requires_value: ClassVar[bool]
    """The clause carries a comparison operand."""

    @classmethod
    @abstractmethod
    def matches(cls, file_path: str, text: str, value: str | None) -> bool:
        """Whether ``file_path``, whose subject text is ``text``, matches."""


class TextMatchType(SourceFilterMatchType):
    """Compares the subject text with the clause's value."""

    requires_value = True

    @staticmethod
    @abstractmethod
    def compare(text: str, value: str) -> bool:
        """Whether ``text`` satisfies this comparison with ``value``."""

    @classmethod
    def matches(cls, file_path: str, text: str, value: str | None) -> bool:
        if value is None:
            raise ValueError(f"{cls.name} source filters require a value.")
        return cls.compare(text, value)

    @classmethod
    def negation(cls) -> type[TextMatchType]:
        """The comparison that holds exactly when this one does not."""

        (negation,) = (
            member
            for member in SourceFilterMatchType.__registry__.values()
            if issubclass(member, NegatedTextMatch) and member.negates is cls
        )
        return negation


class NegatedTextMatch(TextMatchType):
    """Holds exactly when the comparison it negates does not."""

    negates: ClassVar[type[TextMatchType]]

    @classmethod
    def compare(cls, text: str, value: str) -> bool:
        return not cls.negates.compare(text, value)


class TextContains(TextMatchType):
    name = "contains"

    @staticmethod
    def compare(text: str, value: str) -> bool:
        return value in text


class TextContainsRegex(TextMatchType):
    name = "contains_regex"

    @staticmethod
    def compare(text: str, value: str) -> bool:
        return re.search(value, text) is not None


class TextDoesNotContain(NegatedTextMatch):
    name = "does_not_contain"
    negates = TextContains


class TextDoesNotContainRegex(NegatedTextMatch):
    name = "does_not_contain_regex"
    negates = TextContainsRegex


class TextEquals(TextMatchType):
    name = "equals"

    @staticmethod
    def compare(text: str, value: str) -> bool:
        return text == value


class TextDoesNotEqual(NegatedTextMatch):
    name = "does_not_equal"
    negates = TextEquals


class TextStartsWith(TextMatchType):
    name = "starts_with"

    @staticmethod
    def compare(text: str, value: str) -> bool:
        return text.startswith(value)


class TextDoesNotStartWith(NegatedTextMatch):
    name = "does_not_start_with"
    negates = TextStartsWith


class TextEndsWith(TextMatchType):
    name = "ends_with"

    @staticmethod
    def compare(text: str, value: str) -> bool:
        return text.endswith(value)


class TextDoesNotEndWith(NegatedTextMatch):
    name = "does_not_end_with"
    negates = TextEndsWith


class PathMatchType(SourceFilterMatchType):
    """A predicate of the whole path; the clause carries no value."""

    requires_value = False

    @staticmethod
    @abstractmethod
    def holds_for(file_path: str) -> bool:
        """Whether ``file_path`` satisfies this predicate."""

    @classmethod
    def matches(cls, file_path: str, text: str, value: str | None) -> bool:
        if value is not None:
            raise ValueError(f"{cls.name} source filters do not accept a value.")
        return cls.holds_for(file_path)


class PathIsImage(PathMatchType):
    """The path's extension names a loadable pixel format."""

    name = "is_image"

    @staticmethod
    def holds_for(file_path: str) -> bool:
        suffix = os.path.splitext(file_path)[1].lower()
        try:
            file_format = get_format_from_extension(suffix)
        except ValueError:
            return False
        return file_format.is_pixel_payload


class PathIsTif(PathMatchType):
    name = "is_tif"

    @staticmethod
    def holds_for(file_path: str) -> bool:
        return os.path.splitext(file_path)[1].lower() in {".tif", ".tiff"}


@dataclass(frozen=True, slots=True)
class SourceFilterClause:
    """Typed filter clause applied before metadata extraction."""

    subject: Annotated[
        type[SourceFilterSubject], RegisteredClassChoices(SourceFilterSubject)
    ]
    """Part of the source path inspected by this clause."""

    match_type: Annotated[
        type[SourceFilterMatchType], RegisteredClassChoices(SourceFilterMatchType)
    ]
    """Comparison applied to the selected path text."""

    value: str | None = None
    """Comparison operand; omitted for path predicates such as ``PathIsImage``."""

    any_group: int | None = None
    """Optional OR-group identifier.

    Clauses without a group must all match. Clauses sharing a non-negative group
    are alternatives, and at least one clause in every declared group must match.
    """

    def __post_init__(self) -> None:
        if self.any_group is not None:
            if not isinstance(self.any_group, int) or self.any_group < 0:
                raise ValueError(
                    "SourceFilterClause.any_group must be a nonnegative integer."
                )
        if not self.match_type.requires_value:
            object.__setattr__(self, "value", None)
            return
        if self.value is None:
            raise ValueError(
                f"SourceFilterClause.value is required for {self.match_type.name}."
            )
        object.__setattr__(self, "value", str(self.value))

    def matches(self, file_path: str) -> bool:
        """Whether one source path satisfies this clause."""

        return self.match_type.matches(
            file_path, self.subject.text_of(file_path), self.value
        )


def _normalized_optional_source_text(value: str | None) -> str | None:
    if value is None:
        return None
    return str(value).strip() or None


@dataclass(frozen=True, slots=True)
class ImagePlaneSource:
    """One explicit image-plane source URI declared by a source config."""

    uri: str
    """Local path or supported URI identifying the source image file."""

    series: str | None = None
    """Optional format-specific image-series identifier within the source file."""

    index: str | None = None
    """Optional format-specific plane or image index within the selected series."""

    colour_sample: str | None = None
    """Optional colour-sample identifier within the selected image or plane."""

    def __post_init__(self) -> None:
        normalized_uri = self.uri.strip()
        if not normalized_uri:
            raise ValueError("ImagePlaneSource.uri cannot be empty.")
        object.__setattr__(self, "uri", normalized_uri)
        for field_name in ("series", "index", "colour_sample"):
            object.__setattr__(
                self,
                field_name,
                _normalized_optional_source_text(getattr(self, field_name)),
            )

    def resolved(self, source_root: Path) -> ImagePlaneSource:
        """Return this source with its URI resolved to one verified local file."""

        return replace(self, uri=str(resolve_source_file(self.uri, source_root)))


@dataclass(frozen=True, slots=True)
class ImportedMetadataJoin:
    """One join key between image metadata and an imported metadata table."""

    image_metadata_field: str
    """Field on an image-source metadata record used as the join key."""

    imported_metadata_field: str
    """Column in the imported table matched to ``image_metadata_field``."""

    def __post_init__(self) -> None:
        image_field = self.image_metadata_field.strip()
        imported_field = self.imported_metadata_field.strip()
        if not image_field:
            raise ValueError(
                "ImportedMetadataJoin.image_metadata_field cannot be empty."
            )
        if not imported_field:
            raise ValueError(
                "ImportedMetadataJoin.imported_metadata_field cannot be empty."
            )
        object.__setattr__(self, "image_metadata_field", image_field)
        object.__setattr__(self, "imported_metadata_field", imported_field)


@dataclass(frozen=True, slots=True)
class ImportedMetadataTable:
    """Pipeline-level metadata imported from an external table."""

    location: str | None = None
    """Local path or supported URI for the table; relative paths use the source root."""

    joins: tuple[ImportedMetadataJoin, ...] = ()
    """Field pairs used to attach table rows to image-source metadata records."""

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "location",
            _normalized_optional_source_text(self.location),
        )
        object.__setattr__(
            self,
            "joins",
            normalize_source_binding_values(
                "ImportedMetadataTable.joins",
                self.joins,
                ImportedMetadataJoin,
            ),
        )

    def resolved(
        self,
        source_root: Path,
        *,
        portable_roots: Sequence[Path] = (),
    ) -> ImportedMetadataTable:
        """Return this table resolved against declared portable source roots."""

        if self.location is None:
            return self
        return replace(
            self,
            location=str(
                _resolved_imported_metadata_location(
                    self.location,
                    source_root,
                    portable_roots=portable_roots,
                )
            ),
        )


def _resolved_imported_metadata_location(
    location: str,
    source_root: Path,
    *,
    portable_roots: Sequence[Path] = (),
) -> Path:
    """Resolve imported metadata against explicit portable root anchors."""

    path = _declared_local_source_path(location)
    if path is not None:
        if not path.is_absolute():
            primary = (Path(source_root) / path).resolve()
            if primary.is_file():
                return primary
            portable_matches = tuple(
                dict.fromkeys(
                    candidate.resolve()
                    for root in portable_roots
                    for candidate in (Path(root) / path,)
                    if candidate.is_file()
                )
            )
            if len(portable_matches) > 1:
                raise ValueError(
                    f"Declared source file {location!r} matches multiple portable "
                    f"roots: {tuple(str(candidate) for candidate in portable_matches)!r}."
                )
            if portable_matches:
                return portable_matches[0]
        portable_path = _portable_root_anchored_source_path(
            path,
            (Path(source_root), *(Path(root) for root in portable_roots)),
        )
        if portable_path is not None:
            return resolve_source_file(str(portable_path), source_root)
    return resolve_source_file(location, source_root)


def resolve_source_file(location: str, source_root: Path) -> Path:
    """Resolve a declared local or HTTP source into one verified local path."""

    path = _declared_local_source_path(location)
    if path is not None:
        resolved = path if path.is_absolute() else Path(source_root) / path
        resolved = resolved.resolve()
        if not resolved.is_file():
            raise FileNotFoundError(f"Declared source file does not exist: {resolved}")
        return resolved
    parsed = urlsplit(location)
    if parsed.scheme in ("http", "https"):
        return _materialized_http_source(location, parsed.path)
    raise ValueError(
        f"Unsupported source URI scheme {parsed.scheme!r} in {location!r}."
    )


def _declared_local_source_path(location: str) -> Path | None:
    """Distinguish filesystem paths, including Windows drives, from URI schemes."""

    parsed = urlsplit(location)
    if parsed.scheme == "file":
        if parsed.netloc not in ("", "localhost"):
            raise ValueError(
                f"Unsupported non-local file URI authority in {location!r}."
            )
        return Path(unquote(parsed.path))
    if parsed.scheme == "" or PureWindowsPath(location).is_absolute():
        return Path(location)
    return None


def _portable_root_anchored_source_path(
    declared_path: Path,
    portable_roots: Sequence[Path],
) -> Path | None:
    """Rebase a stale path only when it names an explicit portable root."""

    parts = declared_path.parts
    candidates: list[Path] = []
    for root in portable_roots:
        anchor_indexes = tuple(
            index for index, part in enumerate(parts) if part == root.name
        )
        if not anchor_indexes:
            continue
        tail = parts[anchor_indexes[-1] + 1 :]
        if not tail:
            continue
        candidates.append(root.joinpath(*tail))

    unique_candidates = tuple(dict.fromkeys(candidates))
    if len(unique_candidates) > 1:
        raise ValueError(
            f"Declared source path {declared_path!s} matches multiple portable roots: "
            f"{tuple(str(candidate) for candidate in unique_candidates)!r}."
        )
    return unique_candidates[0] if unique_candidates else None


def _materialized_http_source(uri: str, uri_path: str) -> Path:
    """Materialize one HTTP source atomically in its deterministic XDG cache."""

    cache_dir = (
        get_openhcs_cache_dir()
        / "source_imports"
        / hashlib.sha256(uri.encode("utf-8")).hexdigest()
    )
    suffix = Path(unquote(uri_path)).suffix
    if cache_dir.is_dir():
        cached = tuple(
            path
            for path in cache_dir.iterdir()
            if path.is_file() and path.suffix == suffix and len(path.stem) == 64
        )
        if len(cached) == 1:
            return cached[0]

    request = urllib.request.Request(uri, headers={"User-Agent": "OpenHCS"})
    with urllib.request.urlopen(request, timeout=60) as response:
        payload = response.read()
    content_digest = hashlib.sha256(payload).hexdigest()
    target = cache_dir / f"{content_digest}{suffix}"
    if target.is_file():
        return target

    cache_dir.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(dir=cache_dir)
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_path, target)
    finally:
        temporary_path.unlink(missing_ok=True)
    return target


def normalize_source_binding_values(
    field_name: str,
    values: tuple[SourceBindingValue, ...],
    value_type: type[SourceBindingValue],
) -> tuple[SourceBindingValue, ...]:
    """Return a typed tuple for one source-binding field."""

    normalized_values = tuple(values)
    for value in normalized_values:
        if not isinstance(value, value_type):
            raise TypeError(
                f"{field_name} must contain {value_type.__name__} "
                f"values, got {type(value).__name__}."
            )
    return normalized_values


@dataclass(frozen=True, slots=True)
class MetadataExtractionRule:
    """Regex-backed metadata extraction rule for source binding resolution."""

    source: Annotated[type[MetadataSource], RegisteredClassChoices(MetadataSource)]
    """Source-path text searched by the regular expression."""

    pattern: str
    """Regular expression containing one or more named metadata capture groups."""

    filters: tuple[SourceFilterClause, ...] = ()
    """Optional path clauses limiting which sources this extraction rule processes."""

    def __post_init__(self) -> None:
        if not self.pattern:
            raise ValueError("MetadataExtractionRule.pattern cannot be empty.")
        compiled_pattern = re.compile(str(self.pattern))
        if not compiled_pattern.groupindex:
            raise ValueError(
                "MetadataExtractionRule.pattern must define at least one named "
                "capture group."
            )
        object.__setattr__(self, "pattern", str(self.pattern))
        object.__setattr__(
            self,
            "filters",
            normalize_source_binding_values(
                "MetadataExtractionRule.filters",
                self.filters,
                SourceFilterClause,
            ),
        )

    @property
    def capture_fields(self) -> tuple[str, ...]:
        """Return named metadata fields in their regex declaration order."""

        return tuple(re.compile(self.pattern).groupindex)


@dataclass(frozen=True, slots=True)
class SourceBindingMatchField:
    """Metadata field from one alias used as a source-set pairing key."""

    alias: str
    """Declared source-binding alias contributing one side of the pairing key."""

    metadata_field: str
    """Metadata field read from that alias when constructing the shared key."""

    def __post_init__(self) -> None:
        _require_name(self.alias, "SourceBindingMatchField.alias")
        _require_name(
            self.metadata_field,
            "SourceBindingMatchField.metadata_field",
        )
        object.__setattr__(self, "alias", str(self.alias))
        object.__setattr__(self, "metadata_field", str(self.metadata_field))


@dataclass(frozen=True, slots=True)
class SourceBindingMatchDimension:
    """One shared source-set key, expressed as alias-to-metadata-field pairs."""

    fields: tuple[SourceBindingMatchField, ...] = ()
    """One metadata-field declaration for each alias participating in this key."""

    def __post_init__(self) -> None:
        fields = normalize_source_binding_values(
            "SourceBindingMatchDimension.fields",
            self.fields,
            SourceBindingMatchField,
        )
        aliases = tuple(match_field.alias for match_field in fields)
        duplicate = next(
            (alias for index, alias in enumerate(aliases) if alias in aliases[:index]),
            None,
        )
        if duplicate is not None:
            raise ValueError(
                f"SourceBindingMatchDimension contains duplicate alias {duplicate!r}."
            )
        object.__setattr__(self, "fields", fields)

    def field_for_alias(self, alias: str) -> str | None:
        for match_field in self.fields:
            if match_field.alias == alias:
                return match_field.metadata_field
        return None


@dataclass(frozen=True, slots=True)
class SourceSetPairing(ABC, metaclass=AutoRegisterMeta):
    """How the matched source aliases are paired into logical source sets.

    Each way of pairing is a subclass. ``name`` is its spelling in forms and in
    CellProfiler's NamesAndTypes "Image set matching method" setting.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None

    dimensions: ClassVar[tuple[SourceBindingMatchDimension, ...]] = ()
    """Shared metadata keys pairing the aliases; none when pairing by order."""

    @classmethod
    def keyed_by(
        cls, dimensions: tuple[SourceBindingMatchDimension, ...]
    ) -> SourceSetPairing:
        """This pairing keyed by ``dimensions``; pairing by order takes no keys."""

        return cls()

    @staticmethod
    def named(name: str) -> type[SourceSetPairing]:
        """Return the pairing class spelled ``name`` (case-insensitive)."""

        pairing = SourceSetPairing.__registry__.get(name.strip().casefold())
        if pairing is None:
            raise ValueError(
                f"Unknown source-set pairing {name!r}; expected one of "
                f"{tuple(SourceSetPairing.__registry__)!r}."
            )
        return pairing


@dataclass(frozen=True, slots=True)
class PairByOrder(SourceSetPairing):
    """Pair the aliases' sources by their deterministic source order."""

    name = "order"


@dataclass(frozen=True, slots=True)
class PairByMetadata(SourceSetPairing):
    """Pair the aliases' sources by shared metadata keys."""

    name = "metadata"

    dimensions: tuple[SourceBindingMatchDimension, ...] = ()
    """Ordered shared metadata keys; each names one field per alias."""

    @classmethod
    def keyed_by(
        cls, dimensions: tuple[SourceBindingMatchDimension, ...]
    ) -> SourceSetPairing:
        return cls(dimensions=dimensions)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "dimensions",
            normalize_source_binding_values(
                "PairByMetadata.dimensions",
                self.dimensions,
                SourceBindingMatchDimension,
            ),
        )


@dataclass(frozen=True, slots=True)
class ComponentSelector:
    """Component-axis key/value pair used either to select sources or assign identity."""

    component: Annotated[type[Axis], AxisChoices()]
    """Declared axis of the active family, such as channel, site, Z index, or timepoint."""

    value: str
    """Exact semantic value selected or assigned for ``component``."""

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "component",
            _coerce_component(self.component, "ComponentSelector.component"),
        )
        if self.value == "":
            raise ValueError("ComponentSelector.value cannot be empty.")
        object.__setattr__(self, "value", str(self.value))


@dataclass(frozen=True, slots=True)
class MetadataSelector:
    """Metadata field/value filter used to select source candidates for one alias."""

    field: str
    """Source metadata field compared during selector resolution."""

    value: SourceMetadataScalar
    """Exact scalar value required in the selected metadata field."""

    def __post_init__(self) -> None:
        _require_name(self.field, "MetadataSelector.field")
        if self.value is None or self.value == "":
            raise ValueError("MetadataSelector.value cannot be empty.")
        object.__setattr__(self, "field", str(self.field))
        object.__setattr__(self, "value", source_metadata_scalar(self.value))


@dataclass(frozen=True, slots=True)
class SourceSelector:
    """Choose store-emitted image planes for one named pipeline input.

    Component and metadata selectors use declared plane identity. Path filters use
    source provenance supplied by the owning image store; they never decode a
    storage format or infer its axes.
    """

    components: Annotated[tuple[ComponentSelector, ...], FieldLabel("Select Axes")] = ()
    """Component constraints used to choose sources, for example channel=1.

    This filters candidates; it does not assign the output identity.
    """

    metadata: Annotated[tuple[MetadataSelector, ...], FieldLabel("Select Metadata")] = ()
    """Exact metadata field/value pairs required on selected sources, e.g. Well=A01.

    This filters candidates; pairing sources into sets uses the match plan.
    """

    filters: Annotated[tuple[SourceFilterClause, ...], FieldLabel("Select Files")] = ()
    """Path-based clauses applied to source provenance before selection."""

    inherit_current_scope: bool = True
    """Retain the current execution-scope coordinates while resolving this selector."""

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "components",
            normalize_source_binding_values(
                "SourceSelector.components",
                self.components,
                ComponentSelector,
            ),
        )
        object.__setattr__(
            self,
            "metadata",
            normalize_source_binding_values(
                "SourceSelector.metadata",
                self.metadata,
                MetadataSelector,
            ),
        )
        object.__setattr__(
            self,
            "filters",
            normalize_source_binding_values(
                "SourceSelector.filters",
                self.filters,
                SourceFilterClause,
            ),
        )

    def path_filters_match(self, identities: tuple[str, ...]) -> bool:
        """Match store-owned path provenance, without guessing decoded identity."""
        from openhcs.core.source_matching import source_filters_match

        return any(source_filters_match(path, self.filters) for path in identities)

    def metadata_candidates_match(
        self,
        candidates: Iterable[SourceMetadataMapping],
    ) -> bool:
        """Match declared coordinates in store or current-payload metadata."""
        from openhcs.core.source_matching import (
            semantic_source_metadata_value,
            source_component_metadata_values,
            source_metadata_values_equal,
        )

        candidates = tuple(candidates)
        return all(
            any(
                source_metadata_values_equal(value, selector.value)
                for metadata in candidates
                for value in source_component_metadata_values(metadata, selector.component)
            )
            for selector in self.components
        ) and all(
            any(
                value is not None and source_metadata_values_equal(value, selector.value)
                for metadata in candidates
                for value in (semantic_source_metadata_value(metadata, selector.field),)
            )
            for selector in self.metadata
        )

    def matches_provenance(self, provenance: SourceImageProvenance) -> bool:
        """Apply the same selectors to identities carried by current pixels."""
        identities = provenance.represented_source_identities
        return (
            (not self.filters or self.path_filters_match(
                tuple(path for identity in identities for path in identity.filter_paths)
            ))
            and self.metadata_candidates_match(
                tuple(identity.component_metadata or {} for identity in identities)
            )
        )


def source_alias_measurement_names(alias: str) -> tuple[str, ...]:
    """Return measurement source-name tokens represented by a source alias."""
    normalized_alias = alias.strip()
    if not normalized_alias:
        return ()
    parts = tuple(
        part for part in normalized_alias.split(SOURCE_ALIAS_PART_SEPARATOR) if part
    )
    return parts or (normalized_alias,)


@dataclass(frozen=True, slots=True)
class SourceAssignmentBase(metaclass=AutoRegisterMeta):
    """Shared contract for selecting an alias and assigning its semantic identity."""

    __registry_key__ = "assignment_kind"
    __skip_if_no_key__ = True
    assignment_kind: ClassVar[str | None] = None

    alias: str
    """Stable input name presented to pipeline functions and user interfaces."""

    selector: SourceSelector = SourceSelector()
    """Source-plane selection criteria for this named input."""

    origin: Annotated[
        type[SourceBindingOrigin], RegisteredClassChoices(SourceBindingOrigin)
    ] = FromStepInput
    """Whether selection starts from the prior step input or pipeline-start sources."""

    component_identity: Annotated[
        tuple[ComponentSelector, ...], FieldLabel("Assign Axes")
    ] = ()
    """Semantic component identity attached after selection, for example channel=1.

    Outputs use it when they cannot inherit identity from a concrete input path.
    """

    def __post_init__(self) -> None:
        normalized_alias = str(self.alias).strip()
        if not normalized_alias:
            raise ValueError(f"{type(self).__name__}.alias cannot be empty.")
        object.__setattr__(self, "alias", normalized_alias)
        if not isinstance(self.selector, SourceSelector):
            raise TypeError(
                f"{type(self).__name__}.selector must be SourceSelector, "
                f"got {type(self.selector).__name__}."
            )
        component_identity = normalize_source_binding_values(
            f"{type(self).__name__}.component_identity",
            self.component_identity,
            ComponentSelector,
        )
        seen_components: dict[type[Axis], str] = {}
        for selector in component_identity:
            existing = seen_components.get(selector.component)
            if existing is not None and existing != selector.value:
                raise ValueError(
                    f"{type(self).__name__}.component_identity contains "
                    f"conflicting {selector.component.name!r} values "
                    f"{existing!r} and {selector.value!r}."
                )
            seen_components[selector.component] = selector.value
        object.__setattr__(
            self,
            "component_identity",
            tuple(dict.fromkeys(component_identity)),
        )

    @property
    def artifact_kind(self) -> ArtifactType:
        """Artifact kind bound by this source assignment."""
        raise NotImplementedError(f"{type(self).__name__} must provide artifact_kind.")

    @property
    def measurement_source_names(self) -> tuple[str, ...]:
        """Return measurement feature source qualifiers declared by this alias."""
        if not self.artifact_kind.participates_in_measurement_source_names:
            return ()
        return source_alias_measurement_names(self.alias)

    def component_identity_with(
        self,
        selector: ComponentSelector,
    ) -> tuple[ComponentSelector, ...]:
        """Return component identity extended by one non-conflicting selector."""
        if not isinstance(selector, ComponentSelector):
            raise TypeError(
                f"{type(self).__name__}.component_identity selector must be "
                f"ComponentSelector, got {type(selector).__name__}."
            )
        for existing in self.component_identity:
            if existing.component is not selector.component:
                continue
            if existing.value != selector.value:
                raise ValueError(
                    f"Source assignment {self.alias!r} declares "
                    f"{selector.component.name!r} identity {existing.value!r}, "
                    f"but {selector.value!r} was requested."
                )
            return self.component_identity
        return (*self.component_identity, selector)

    def is_compatible_with_component_group(
        self,
        component: type[Axis],
        group_key: str,
    ) -> bool:
        """Return whether this identity permits one typed execution group."""

        component_selectors = tuple(
            selector
            for selector in self.component_identity
            if selector.component is component
        )
        return not component_selectors or any(
            selector.value == group_key for selector in component_selectors
        )

    def requires_cross_group_candidate_resolution(
        self,
        component: type[Axis],
        group_key: str,
    ) -> bool:
        """Return whether assigned identity differs from its selected coordinate."""

        normalized_component = _coerce_component(
            component,
            f"{type(self).__name__}.requires_cross_group_candidate_resolution.component",
        )
        normalized_group_key = str(group_key)
        assigned_values = tuple(
            selector.value
            for selector in self.component_identity
            if selector.component is normalized_component
        )
        if normalized_group_key not in assigned_values:
            return False
        selected_values = tuple(
            selector.value
            for selector in self.selector.components
            if selector.component is normalized_component
        )
        return normalized_group_key not in selected_values

    def with_component_identity(self, selector: ComponentSelector) -> Self:
        """Return this source assignment with one canonical component identity."""
        return replace(
            self,
            component_identity=self.component_identity_with(selector),
        )


@dataclass(frozen=True, slots=True)
class NamedSourceBinding(SourceAssignmentBase):
    """Name selected image planes and their optional component identity.

    ``alias`` is the source name presented to pipeline functions and user
    interfaces. ``origin`` selects current-step pixels or original store pixels;
    both retain their declared acquisition provenance.
    ``component_identity`` authoritatively assigns biological coordinates after
    selector resolution, replacing coordinates merely inferred by a source store.
    """

    assignment_kind = "named_source_binding"
    artifact_kind: type[ArtifactType] = ImageArtifactType
    """Nominal artifact type supplied to the pipeline under this alias."""

    required: bool = True
    """Whether compilation fails when this alias cannot supply an artifact."""

    source_set_role: Annotated[
        type[SourceSetRole], RegisteredClassChoices(SourceSetRole)
    ] = MatchedSource
    """Whether this alias determines source-set membership or broadcasts to every set."""

    projection_role: Annotated[
        type[SourceProjectionRole], RegisteredClassChoices(SourceProjectionRole)
    ] = PrimaryPlaneRole
    """Whether the resolved source becomes a primary image plane or source artifact."""

    explicit_source: ImagePlaneSource | None = None
    """Optional exact image-plane source used instead of selector-based discovery."""

    load_as_monochrome: bool = False
    """Request monochrome loading for a colour source before pipeline processing."""

    load_as_mask: bool = False
    """Interpret the loaded source as a mask rather than an intensity image."""

    source_channel_axis: int | None = None
    """Optional array axis containing channels in the loaded source payload."""

    source_channel_counts: frozenset[int] | None = None
    """Allowed channel-axis lengths used to validate loaded source shapes."""

    def __post_init__(self) -> None:
        SourceAssignmentBase.__post_init__(self)
        object.__setattr__(
            self,
            "artifact_kind",
            ArtifactType.coerce(self.artifact_kind),
        )
        self.projection_role.check_artifact_kind(self.artifact_kind)
        if self.explicit_source is not None and not isinstance(
            self.explicit_source,
            ImagePlaneSource,
        ):
            raise TypeError(
                "NamedSourceBinding.explicit_source must be ImagePlaneSource or None."
            )
        object.__setattr__(self, "required", bool(self.required))
        object.__setattr__(self, "load_as_monochrome", bool(self.load_as_monochrome))
        object.__setattr__(self, "load_as_mask", bool(self.load_as_mask))
        source_channel_axis = self.source_channel_axis
        if source_channel_axis is not None and (
            not isinstance(source_channel_axis, int)
            or isinstance(source_channel_axis, bool)
        ):
            raise TypeError(
                "NamedSourceBinding.source_channel_axis must be int or None."
            )
        source_channel_counts = self.source_channel_counts
        if source_channel_counts is not None:
            if source_channel_axis is None:
                raise ValueError(
                    "NamedSourceBinding source channel counts require a channel axis."
                )
            normalized_counts = frozenset(int(value) for value in source_channel_counts)
            if any(
                isinstance(value, bool) or int(value) <= 0
                for value in source_channel_counts
            ):
                raise ValueError(
                    "NamedSourceBinding.source_channel_counts must contain positive "
                    "integers."
                )
            source_channel_counts = normalized_counts
        object.__setattr__(self, "source_channel_axis", source_channel_axis)
        object.__setattr__(self, "source_channel_counts", source_channel_counts)

    def physical_path_matches(
        self,
        source_root: Path,
        source_path: str | Path,
        path_identities: tuple[str, ...],
    ) -> bool:
        """Admit one physical source using exact identity and path provenance.

        Companion identities may satisfy selector filters, but do not replace
        the exact source URI. Metadata/components require subsequent decoding.
        """
        if self.explicit_source is not None:
            explicit_path = Path(self.explicit_source.resolved(source_root).uri)
            candidate_path = Path(source_path)
            if not candidate_path.is_absolute():
                candidate_path = source_root / candidate_path
            if not source_paths_equal(candidate_path.resolve(), explicit_path):
                return False
        return self.selector.path_filters_match(path_identities)

    def with_resolved_explicit_source(self, source_root: Path) -> Self:
        """Return this binding with its explicit source resolved to a local file."""

        if self.explicit_source is None:
            return self
        return replace(
            self, explicit_source=self.explicit_source.resolved(source_root)
        )

    def source_channel_axis_for_shape(
        self,
        shape: tuple[int, ...],
        *,
        source_axis_count: int = 0,
        observed_axis: int | None = None,
    ) -> int | None:
        """Resolve the binding and loaded-payload channel-axis declarations."""

        axis = self.source_channel_axis
        if len(shape) == source_axis_count + 2:
            return None
        normalized_axis = None
        if axis is not None:
            normalized_axis = axis if axis >= 0 else len(shape) + axis
            if normalized_axis < source_axis_count or normalized_axis >= len(shape):
                raise ValueError(
                    f"Source binding {self.alias!r} channel axis {axis} is "
                    f"incompatible with source shape {shape!r} and "
                    f"{source_axis_count} leading axes."
                )
            counts = self.source_channel_counts
            if counts is not None and shape[normalized_axis] not in counts:
                raise ValueError(
                    f"Source binding {self.alias!r} declares channel axis {axis} "
                    f"with cardinality in {tuple(sorted(counts))!r}, but source "
                    f"shape {shape!r} carries {shape[normalized_axis]} channels."
                )
        if observed_axis is None:
            return axis
        normalized_observed_axis = (
            observed_axis if observed_axis >= 0 else len(shape) + observed_axis
        )
        if (
            normalized_observed_axis < source_axis_count
            or normalized_observed_axis >= len(shape)
        ):
            raise ValueError(
                f"Loaded source channel axis {observed_axis} for binding "
                f"{self.alias!r} is incompatible with source shape {shape!r} and "
                f"{source_axis_count} leading axes."
            )
        if normalized_axis is not None and normalized_axis != normalized_observed_axis:
            raise ValueError(
                f"Source binding {self.alias!r} channel axis {axis} conflicts with "
                f"loaded payload channel axis {observed_axis}."
            )
        return observed_axis

    def input_spec(self) -> ArtifactSpec:
        """Project this source declaration into its canonical artifact input."""

        return ArtifactSpec.input(
            self.alias,
            self.artifact_kind,
            required=self.required,
        )

    def apply_loaded_payload(
        self,
        payload: RuntimeArrayData,
        source_context: ImagePayloadSourceMetadataContext | None,
    ) -> RuntimeArrayData:
        """Apply this declaration to one freshly loaded source payload."""
        import numpy as np

        from openhcs.core.axes import ColourAxis
        from openhcs.core.payload_axes import PayloadAxes
        from openhcs.core.runtime_image_values import (
            ImagePayload,
            ImagePayloadMetadata,
            ImageUnitIntervalIntensityMetadata,
        )

        payload = ImagePayload.of(payload)
        if source_context is None:
            existing = payload.metadata
            metadata = (
                existing
                if existing.has_values
                else ImagePayloadMetadata.for_array_payload(payload.data)
            )
        else:
            # The physical context needs the declared channel axis before it
            # admits source geometry. It resolves this binding's axis once.
            metadata = source_context.metadata(payload, source_binding=self)
        metadata = metadata.replace_fields(
            source_provenance=metadata.source_provenance.with_source_image_names(
                (self.alias,)
            )
        )
        if source_context is None:
            metadata = metadata.replace_fields(
                axes=PayloadAxes.colour_samples(
                    self.source_channel_axis_for_shape(
                        np.shape(payload.data),
                        observed_axis=metadata.axis_position(ColourAxis),
                    )
                ),
            )
        metadata.axis_index(ColourAxis, payload)

        data, colour_axis_position = self.artifact_kind.normalize_source_payload(
            payload.data,
            metadata.axis_position(ColourAxis),
        )
        if self.load_as_monochrome and colour_axis_position is not None:
            data = self._monochrome_source_data(data, colour_axis_position, metadata)
            colour_axis_position = None
            metadata = metadata.replace_fields(
                unit_interval_intensity=ImageUnitIntervalIntensityMetadata(),
            )
        if self.load_as_mask:
            data = np.asarray(data, dtype=bool)
            metadata = metadata.replace_fields(
                unit_interval_intensity=ImageUnitIntervalIntensityMetadata(scale=1),
            )

        metadata = metadata.replace_fields(
            axes=PayloadAxes.colour_samples(colour_axis_position)
        )
        return metadata.payload_with(data, payload.mask)

    def project_step_input_payload(self, payload: RuntimeArrayData) -> RuntimeArrayData:
        """Select current pixels by provenance, then assign this binding's name.

        An existing alias selects its represented current planes before applying
        selectors. A new alias names the selector's current-plane selection.
        Neither case reloads original pixels.
        """

        metadata = payload.metadata
        provenance = metadata.source_provenance
        if not provenance.has_values:
            raise ValueError(f"Step-input binding {self.alias!r} requires source provenance.")

        if not provenance.source_plane_count:
            if not self.selector.matches_provenance(provenance):
                raise ValueError(f"Step-input binding {self.alias!r} selects no current planes.")
            selected = payload
        else:
            named_planes = provenance.source_plane_selection(self.alias)
            candidate_planes = (
                range(provenance.source_plane_count)
                if named_planes is None else named_planes
            )
            selection = tuple(
                index for index in candidate_planes
                if self.selector.matches_provenance(provenance.for_source_plane(index))
            )
            if not selection:
                raise ValueError(f"Step-input binding {self.alias!r} selects no current planes.")
            selected = metadata.project_source_planes(payload, selection)
        return self.apply_loaded_payload(selected, source_context=None)

    @property
    def requires_current_pixels(self) -> bool:
        """Whether this source projects the actual current main-flow pixels."""
        return (
            self.origin is FromStepInput
            and self.projection_role is PrimaryPlaneRole
        )

    @staticmethod
    def _monochrome_source_data(
        data: RuntimeArrayData,
        channel_axis: int,
        metadata: ImagePayloadMetadata,
    ) -> RuntimeArrayData:
        """Convert declared RGB channels using the source intensity domain."""
        import numpy as np


        normalized = metadata.payload_with(data).normalize_intensity_payload(dtype=np.float32,)
        rgb = np.moveaxis(
            np.asarray(normalized.data), channel_axis, -1
        )[..., :3]
        if np.all(rgb == rgb[..., :1]):
            return np.ascontiguousarray(rgb[..., 0])

        from skimage.color import rgb2gray

        return rgb2gray(rgb)

    def component_values(
        self,
        component: type[Axis],
        *,
        realized_source_metadata: Iterable[SourceMetadataMapping] | None = None,
    ) -> tuple[str, ...]:
        """Return declared or workspace-realized values for one component axis."""

        declared_values = self._declared_component_values(component)
        if declared_values:
            return declared_values

        if realized_source_metadata is None:
            return ()

        from openhcs.core.source_matching import source_component_metadata_values

        values: list[str] = []
        for metadata in realized_source_metadata:
            if not self.matches_realized_source_metadata(metadata):
                continue
            values.extend(source_component_metadata_values(metadata, component))
        return tuple(dict.fromkeys(values))

    def _declared_component_values(
        self, component: type[Axis]
    ) -> tuple[str, ...]:
        """Resolve exact identity values before selector-derived coordinates."""
        for declarations in (self.component_identity, self.selector.components):
            values = tuple(
                selector.value
                for selector in declarations
                if selector.component is component
            )
            if values:
                return values
        return ()

    def component_domains(
        self,
        *,
        realized_source_metadata: Iterable[SourceMetadataMapping] | None = None,
    ) -> Mapping[type[Axis], tuple[str, ...]]:
        """Admit all component domains from the same matched source records."""
        domains = {
            component: values
            for component in AxisFamily.active().axes
            for values in (self._declared_component_values(component),)
            if values
        }
        if realized_source_metadata is None or len(domains) == len(AxisFamily.active().axes):
            return domains
        realized: dict[type[Axis], list[str]] = {}
        for metadata in realized_source_metadata:
            if not self.matches_realized_source_metadata(metadata):
                continue
            for component, values in SourceMetadataFields.component_domains(
                metadata
            ).items():
                if component not in domains:
                    realized.setdefault(component, []).extend(values)
        domains.update(
            (component, tuple(dict.fromkeys(values)))
            for component, values in realized.items()
        )
        return domains

    def matches_realized_source_metadata(
        self,
        metadata: SourceMetadataMapping,
    ) -> bool:
        """Return whether workspace metadata belongs to this source binding."""

        alias_value = metadata.get(SOURCE_BINDING_ALIAS_METADATA_FIELD)
        if isinstance(alias_value, Mapping):
            raise TypeError(
                f"{SOURCE_BINDING_ALIAS_METADATA_FIELD} must be scalar source metadata."
            )
        normalized_alias = source_metadata_scalar(alias_value)
        if normalized_alias is not None:
            return str(normalized_alias) == self.alias

        return self.selector.metadata_candidates_match((metadata,))

    @property
    def requires_selector_resolution(self) -> bool:
        """Whether this binding needs file/metadata-aware source resolution."""

        return bool(
            self.selector.components
            or self.selector.metadata
            or self.selector.filters
            or not self.selector.inherit_current_scope
        )

    def requires_step_input_component_stack(
        self,
        components: tuple[type[Axis], ...],
    ) -> bool:
        """Whether resolving this binding needs component-varying step input."""
        if self.origin is not FromStepInput:
            return False
        if not components:
            return False
        if self.selector.filters or self.selector.metadata:
            return True
        return any(
            selector.component in components for selector in self.selector.components
        )


class SourceBindingDeclarationsMixin:
    """Shared named-binding view for editable and compiled source plans."""

    bindings: tuple[NamedSourceBinding, ...] | None
    source_stack_components: tuple[type[Axis], ...]
    source_spatial_domain: SourceSpatialDomain

    @property
    def binding_declarations(self) -> tuple[NamedSourceBinding, ...]:
        """Named bindings explicitly declared on this plan."""

        return tuple(self.bindings or ())

    @property
    def matched_source_bindings(self) -> tuple[NamedSourceBinding, ...]:
        """Bindings that determine source-set membership and cardinality."""

        return tuple(
            binding
            for binding in self.binding_declarations
            if binding.source_set_role is MatchedSource
        )

    @property
    def broadcast_source_bindings(self) -> tuple[NamedSourceBinding, ...]:
        """Bindings appended to every assembled source set."""

        return tuple(
            binding
            for binding in self.binding_declarations
            if binding.source_set_role is BroadcastSource
        )

    @property
    def primary_plane_bindings(self) -> tuple[NamedSourceBinding, ...]:
        """Bindings materialized as primary image planes."""

        return tuple(
            binding
            for binding in self.binding_declarations
            if binding.projection_role is PrimaryPlaneRole
        )

    def binding_for_alias(
        self,
        alias: str,
    ) -> NamedSourceBinding | None:
        """Return the declaration for one source alias when present."""
        for binding in self.binding_declarations:
            if binding.alias == alias:
                return binding
        return None

    def binding_for_artifact_ref(
        self,
        ref: ArtifactSpecRef,
    ) -> NamedSourceBinding | None:
        """Return the source declaration for one exact artifact input ref."""
        if not isinstance(ref, ArtifactSpecRef):
            raise TypeError(
                "SourceBindingDeclarationsMixin.binding_for_artifact_ref requires "
                f"an ArtifactSpecRef, got {type(ref).__name__}."
            )
        return next(
            (
                binding
                for binding in self.binding_declarations
                if binding.input_spec().ref() == ref
            ),
            None,
        )

    def declares_artifact_ref(self, ref: ArtifactSpecRef) -> bool:
        """Return whether this plan declares one exact artifact input ref."""
        return self.binding_for_artifact_ref(ref) is not None

    @property
    def primary_plane_aliases(self) -> tuple[str, ...]:
        """Return aliases materialized into the primary source image stack."""
        return tuple(binding.alias for binding in self.primary_plane_bindings)

    @property
    def measurement_source_names(self) -> tuple[str, ...]:
        """Return source qualifiers available to measurement feature names."""
        names = {
            name
            for binding in self.binding_declarations
            for name in binding.measurement_source_names
        }
        return tuple(sorted(names, key=str.lower))

    def requires_step_input_component_stack(
        self,
        components: tuple[type[Axis], ...],
    ) -> bool:
        """Whether any declaration needs component-resolved step input."""
        return any(
            binding.requires_step_input_component_stack(components)
            for binding in self.binding_declarations
        )

    @property
    def requires_pipeline_start_resolution(self) -> bool:
        """Whether any declaration resolves from the pipeline-start universe."""
        return any(
            binding.origin is FromPipelineStart
            for binding in self.binding_declarations
        )

    @property
    def requires_pipeline_start_source_set(self) -> bool:
        """Whether pipeline-start declarations form a multi-member source set."""
        return (
            sum(
                1
                for binding in self.binding_declarations
                if binding.origin is FromPipelineStart
                and binding.source_set_role is MatchedSource
            )
            > 1
        )

    @property
    def requires_step_input_selector_resolution(self) -> bool:
        """Whether step-input declarations need selector-aware matching."""
        return any(
            binding.origin is FromStepInput
            and binding.requires_selector_resolution
            for binding in self.binding_declarations
        )

    def bindings_for_component_group(
        self,
        component: type[Axis] | None,
        group_key: str | None,
    ) -> tuple[NamedSourceBinding, ...]:
        """Return bindings compatible with one typed execution group."""
        if component is None and group_key is None:
            return self.binding_declarations
        if component is None or group_key is None:
            raise ValueError(
                "Source binding component grouping requires both component and "
                "group_key, or neither."
            )
        normalized_group_key = str(group_key)
        normalized_component = _coerce_component(
            component,
            "SourceBindingDeclarationsMixin.bindings_for_component_group.component",
        )
        matching_bindings = tuple(
            binding
            for binding in self.binding_declarations
            if binding.is_compatible_with_component_group(
                normalized_component,
                normalized_group_key,
            )
        )
        if not matching_bindings:
            raise ValueError(
                f"No source binding declares {normalized_component.name} "
                f"group {normalized_group_key!r}."
            )
        return matching_bindings

    def requires_cross_group_candidate_resolution(
        self,
        component: type[Axis],
        group_key: str,
    ) -> bool:
        """Return whether this semantic group must search other source groups."""

        if not self.binding_declarations:
            return False
        return any(
            binding.requires_cross_group_candidate_resolution(component, group_key)
            for binding in self.bindings_for_component_group(component, group_key)
        )

    def bindings_for_represented_source_stack(
        self,
        source_image_names: Iterable[str],
        *,
        variable_components: ComponentSet,
    ) -> tuple[NamedSourceBinding, ...]:
        """Return bindings represented directly or across one declared stack."""

        if not isinstance(variable_components, ComponentSet):
            raise TypeError(
                "Source binding stack projection requires a ComponentSet, got "
                f"{type(variable_components).__name__}."
            )
        represented_names = frozenset(str(name) for name in source_image_names)
        represented_bindings = tuple(
            binding
            for binding in self.binding_declarations
            if binding.alias in represented_names
        )

        def belongs_to_represented_stack(binding: NamedSourceBinding) -> bool:
            if binding.alias in represented_names:
                return True
            binding_identity = {
                selector.component: selector.value
                for selector in binding.component_identity
            }
            for represented in represented_bindings:
                represented_identity = {
                    selector.component: selector.value
                    for selector in represented.component_identity
                }
                if binding_identity.keys() != represented_identity.keys():
                    continue
                differing_components = tuple(
                    component
                    for component, value in binding_identity.items()
                    if represented_identity[component] != value
                )
                if differing_components and all(
                    component in variable_components
                    for component in differing_components
                ):
                    return True
            return False

        return tuple(
            binding
            for binding in self.binding_declarations
            if belongs_to_represented_stack(binding)
        )

    def for_represented_source_stack(
        self,
        source_image_names: Iterable[str],
        *,
        variable_components: ComponentSet,
    ) -> Self:
        """Return this plan projected through exact payload source provenance."""

        return replace(
            self,
            bindings=self.bindings_for_represented_source_stack(
                source_image_names,
                variable_components=variable_components,
            ),
        )

    def for_component_group(
        self,
        component: type[Axis],
        group_key: str,
    ) -> Self:
        """Return these declarations scoped to one typed component group."""
        return replace(
            self,
            bindings=self.bindings_for_component_group(component, group_key),
        )

    def for_execution_axis_scope(
        self,
        axis_scope: RuntimeExecutionAxisScope,
    ) -> Self:
        """Project declarations to one typed runtime component coordinate."""

        if not self.has_primary_content or not axis_scope.has_value:
            return self
        component = axis_scope.component
        if component is None:
            raise RuntimeError(
                "A valued runtime execution scope must declare its component."
            )
        return self.for_component_group(
            component,
            axis_scope.require_value_text(),
        )

    def component_group_keys_for_artifact_specs(
        self,
        component: type[Axis],
        specs: Iterable[ArtifactSpec],
        available_artifacts: ArtifactSpecCollection,
        *,
        realized_source_metadata: Iterable[SourceMetadataMapping] | None = None,
    ) -> tuple[str, ...]:
        """Trace artifact group lineage to this plan's component selectors."""

        resolved_component = _coerce_component(
            component,
            "SourceBindingDeclarationsMixin.component_group_keys_for_artifact_specs.component",
        )
        realized_metadata = (
            None
            if realized_source_metadata is None
            else tuple(realized_source_metadata)
        )
        return tuple(
            dict.fromkeys(
                value
                for binding in self.bindings_for_artifact_specs(
                    specs,
                    available_artifacts,
                )
                for value in binding.component_values(
                    resolved_component,
                    realized_source_metadata=realized_metadata,
                )
            )
        )

    def bindings_for_artifact_specs(
        self,
        specs: Iterable[ArtifactSpec],
        available_artifacts: ArtifactSpecCollection,
    ) -> tuple[NamedSourceBinding, ...]:
        """Trace exact artifact group lineage to its source declarations."""

        if not self.binding_declarations:
            return ()

        def source_bindings(
            spec: ArtifactSpec,
            visited: frozenset[ArtifactSpecRef],
        ) -> tuple[NamedSourceBinding, ...]:
            ref = spec.ref()
            if ref in visited:
                return ()
            next_visited = visited | {ref}
            binding = self.binding_for_artifact_ref(ref)
            direct_bindings = (binding,) if binding is not None else ()
            if spec.relations:
                declared_spec = spec
            elif direct_bindings:
                return direct_bindings
            else:
                declared_spec = available_artifacts.by_name_and_artifact_type(
                    spec.name,
                    spec.artifact_type,
                )
                if declared_spec is None:
                    raise ValueError(
                        f"Artifact group lineage references unavailable {ref!r}."
                    )
            relation_bindings: list[NamedSourceBinding] = []
            for source_ref in declared_spec.group_scope_sources():
                source_spec = available_artifacts.by_name_and_artifact_type(
                    source_ref.name,
                    source_ref.artifact_type,
                )
                if (
                    source_spec is None
                    or source_spec.for_plan_type(source_ref.plan_type).ref()
                    != source_ref
                ):
                    raise ValueError(
                        "Artifact group-lineage relation references unavailable "
                        f"source {source_ref!r}."
                    )
                relation_bindings.extend(source_bindings(source_spec, next_visited))
            return tuple(dict.fromkeys((*direct_bindings, *relation_bindings)))

        return self.bindings_for_artifact_refs(
            binding.input_spec().ref()
            for spec in specs
            for binding in source_bindings(spec, frozenset())
        )

    def for_artifact_specs(
        self,
        specs: Iterable[ArtifactSpec],
        available_artifacts: ArtifactSpecCollection,
    ) -> Self:
        """Project these declarations through exact artifact lineage."""

        return replace(
            self,
            bindings=self.bindings_for_artifact_specs(
                specs,
                available_artifacts,
            ),
        )

    def runtime_variable_components_for_artifact_specs(
        self,
        specs: Iterable[ArtifactSpec],
        available_artifacts: ArtifactSpecCollection,
        consumer_variable_components: ComponentSet,
    ) -> ComponentSet | None:
        """Return source axes visible to a consumer, or None without lineage."""

        if not isinstance(consumer_variable_components, ComponentSet):
            raise TypeError(
                "Source binding runtime variable components require a ComponentSet."
            )
        bindings = self.bindings_for_artifact_specs(specs, available_artifacts)
        if not bindings:
            return None

        fixed_components = ComponentSet(
            tuple(
                component
                for component in consumer_variable_components
                for binding_values in (
                    tuple(binding.component_values(component) for binding in bindings),
                )
                if all(len(values) == 1 for values in binding_values)
                and len({values[0] for values in binding_values}) == 1
            )
        )
        return consumer_variable_components.excluding(fixed_components)

    def bindings_for_artifact_refs(
        self,
        artifact_refs: Iterable[ArtifactSpecRef],
    ) -> tuple[NamedSourceBinding, ...]:
        """Return bindings whose exact input refs are selected."""
        refs = frozenset(artifact_refs)
        if any(not isinstance(ref, ArtifactSpecRef) for ref in refs):
            raise TypeError(
                "SourceBindingDeclarationsMixin.bindings_for_artifact_refs "
                "requires ArtifactSpecRef values."
            )
        return tuple(
            binding
            for binding in self.binding_declarations
            if binding.input_spec().ref() in refs
        )

    def for_artifact_refs(
        self,
        artifact_refs: Iterable[ArtifactSpecRef],
    ) -> Self:
        """Return this source-binding config scoped to exact artifact refs."""
        return replace(
            self,
            bindings=self.bindings_for_artifact_refs(artifact_refs),
        )


@dataclass(frozen=True, kw_only=True)
class _SourceBindingPlanBase(ABC):
    """Shared typed source-binding plan fields across editable and compiled views."""

    metadata_rules: tuple[MetadataExtractionRule, ...] = ()
    """Regex/metadata extraction rules that add semantic fields for matching sources."""

    match_plan: SourceSetPairing = PairByOrder()
    """How the matched aliases pair into logical source sets."""

    metadata_fields: tuple[FieldSpec, ...] = ()
    """Exact scalar schema for source-literal metadata fields."""

    def _normalize_common_fields(self) -> None:
        from objectstate.field_value import FieldValue
        from objectstate.field_access import DataclassFieldAccess

        metadata_rules = DataclassFieldAccess.raw_value(self, "metadata_rules")
        if FieldValue.of(metadata_rules).has_value:
            metadata_rules = tuple(metadata_rules)
            for rule in metadata_rules:
                if not isinstance(rule, MetadataExtractionRule):
                    raise TypeError(
                        f"{type(self).__name__}.metadata_rules must contain "
                        "MetadataExtractionRule values, got "
                        f"{type(rule).__name__}."
                    )
        object.__setattr__(self, "metadata_rules", metadata_rules)

        match_plan = DataclassFieldAccess.raw_value(self, "match_plan")
        if FieldValue.of(match_plan).has_value and not isinstance(match_plan, SourceSetPairing | None):
            raise TypeError(
                f"{type(self).__name__}.match_plan must be a SourceSetPairing, "
                f"got {type(match_plan).__name__}."
            )

        metadata_fields = DataclassFieldAccess.raw_value(self, "metadata_fields")
        if FieldValue.of(metadata_fields).has_value:
            metadata_fields = FieldSpec.merge_exact(
                (tuple(metadata_fields),),
                context=f"{type(self).__name__}.metadata_fields",
            )
        object.__setattr__(self, "metadata_fields", metadata_fields)

    @property
    def metadata_rule_declarations(self) -> tuple[MetadataExtractionRule, ...]:
        """Metadata rules explicitly declared on this plan."""

        return tuple(self.metadata_rules or ())

    @property
    @abstractmethod
    def has_primary_content(self) -> bool:
        """Whether the subclass-specific binding payload is empty."""



def source_binding_group_keys_for_group_by(
    source_bindings: SourceBindingDeclarationsMixin,
    group_by: type[GroupingDeclaration],
    *,
    realized_source_metadata: Iterable[SourceMetadataMapping] | None = None,
) -> tuple[str, ...]:
    """Return ordered binding component values for the grouping component."""

    if not isinstance(source_bindings, SourceBindingDeclarationsMixin):
        raise TypeError(
            "source_binding_group_keys_for_group_by requires "
            f"SourceBindingDeclarationsMixin, got {type(source_bindings).__name__}."
        )
    grouping_axes = group_by.grouping_axes()
    if not grouping_axes:
        return ()
    (component,) = grouping_axes
    realized_metadata = (
        None if realized_source_metadata is None else tuple(realized_source_metadata)
    )
    return tuple(
        dict.fromkeys(
            value
            for binding in source_bindings.primary_plane_bindings
            for value in binding.component_values(
                component,
                realized_source_metadata=realized_metadata,
            )
        )
    )



@dataclass(frozen=True, slots=True)
class CompiledSourceBindingPlan(SourceBindingDeclarationsMixin, _SourceBindingPlanBase):
    """Immutable compile-time source binding plan for one step."""

    bindings: tuple[NamedSourceBinding, ...] = ()
    source_stack_components: tuple[type[Axis], ...] = ()
    source_spatial_domain: SourceSpatialDomain = field(
        default_factory=SourceSpatialDomain
    )

    def __post_init__(self) -> None:
        bindings = normalize_source_binding_values(
            "CompiledSourceBindingPlan.bindings",
            self.bindings,
            NamedSourceBinding,
        )
        seen_aliases: set[str] = set()
        for binding in bindings:
            if binding.alias in seen_aliases:
                raise ValueError(
                    "CompiledSourceBindingPlan.bindings contains duplicate alias "
                    f"{binding.alias!r}."
                )
            seen_aliases.add(binding.alias)
        object.__setattr__(self, "bindings", bindings)
        object.__setattr__(
            self,
            "source_stack_components",
            ComponentSet.collect(self.source_stack_components).as_tuple(),
        )
        self._normalize_common_fields()

    @property
    def has_primary_content(self) -> bool:
        return bool(self.bindings)

    def for_main_flow_scope(
        self,
        *,
        component: type[Axis] | None,
        group_key: str | None,
        main_flow_refs: tuple[ArtifactSpecRef, ...] | None,
    ) -> CompiledSourceBindingPlan:
        """Project the image argument separately from invocation dispatch.

        Explicit input refs declare every image consumed by the invocation.
        A grouped object cohort does not reduce that image roster to the cohort's
        channel. Implicit image arguments still follow component dispatch. A
        projection that keeps no binding has empty ``binding_declarations``.
        """

        if main_flow_refs is None:
            return (
                self
                if not self.has_primary_content or group_key is None
                else self.for_component_group(component, group_key)
            )
        return self.for_artifact_refs(main_flow_refs)

    def select_anchors(
        self,
        pattern_list: Sequence[str],
        policy: SourceBoundAnchorPatternPolicy,
        source_context: SourcePatternResolutionContext,
    ) -> tuple[str, ...]:
        """Anchors ``policy`` selects for these bindings; none when nothing is bound."""

        if not self.bindings:
            return ()
        return tuple(
            policy.select(
                pattern_list,
                bindings=self.bindings,
                source_context=source_context,
            )
        )

    def __reduce__(
        self,
    ) -> tuple[
        object,
        tuple[
            tuple[NamedSourceBinding, ...],
            tuple[MetadataExtractionRule, ...],
            SourceSetPairing,
            tuple[FieldSpec, ...],
            tuple[type[Axis], ...],
            SourceSpatialDomain,
        ],
    ]:
        """Serialize source-binding plan state for multiprocessing."""
        return (
            self.__class__._from_pickled_state,
            (
                self.bindings,
                self.metadata_rules,
                self.match_plan,
                self.metadata_fields,
                self.source_stack_components,
                self.source_spatial_domain,
            ),
        )

    @property
    def requires_step_input_selector_resolution(self) -> bool:
        """Whether any step-input binding needs selector-aware source matching."""

        return any(
            binding.origin is FromStepInput
            and binding.requires_selector_resolution
            for binding in self.bindings
        )

    @classmethod
    def _from_pickled_state(
        cls,
        bindings: tuple[NamedSourceBinding, ...],
        metadata_rules: tuple[MetadataExtractionRule, ...],
        match_plan: SourceSetPairing,
        metadata_fields: tuple[FieldSpec, ...],
        source_stack_components: tuple[type[Axis], ...],
        source_spatial_domain: SourceSpatialDomain,
    ) -> CompiledSourceBindingPlan:
        return cls(
            bindings=bindings,
            metadata_rules=metadata_rules,
            match_plan=match_plan,
            metadata_fields=metadata_fields,
            source_stack_components=source_stack_components,
            source_spatial_domain=source_spatial_domain,
        )


@dataclass(frozen=True, slots=True)
class CompiledSourceUniversePlan:
    """Frozen source-file universe decisions for one compiled step."""

    requires_step_input_selector_resolution: bool = False
    uses_pipeline_start_binding_origin: bool = False

    @classmethod
    def from_source_binding_plan(
        cls,
        source_binding_plan: CompiledSourceBindingPlan,
    ) -> CompiledSourceUniversePlan:
        uses_pipeline_start_binding_origin = (
            source_binding_plan.has_primary_content
            and any(
                binding.origin is FromPipelineStart
                for binding in source_binding_plan.bindings
            )
        )
        return cls(
            requires_step_input_selector_resolution=(
                source_binding_plan.requires_step_input_selector_resolution
            ),
            uses_pipeline_start_binding_origin=uses_pipeline_start_binding_origin,
        )


@dataclass(frozen=True, slots=True)
class SourceBindingRuntimeMetadataNormalizer:
    """Normalize source metadata carried by a runtime source-binding context."""

    source_metadata_by_path: Mapping[str, SourceMetadataMapping]

    def normalized(self) -> Mapping[str, SourceMetadataMapping]:
        return MappingProxyType(
            {
                str(path): ResolvedSourceMetadataRecord.normalized_mapping(
                    source_metadata_dict(metadata)
                )
                for path, metadata in self.source_metadata_by_path.items()
            }
        )


def _coerce_component(value: Any, field_name: str) -> type[Axis]:
    try:
        return AxisFamily.active().require(value)
    except TypeError as error:
        raise TypeError(f"{field_name}: {error}") from error



def _require_name(value: str, field_name: str) -> None:
    if not value:
        raise ValueError(f"{field_name} cannot be empty.")
