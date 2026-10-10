"""Centralized output filename identity for FunctionStep main-flow writes."""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from pathlib import Path
import re
from typing import ClassVar, Mapping, Sequence, TypeAlias

from openhcs.core.source_path_identity import source_path_identity
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
)
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.components.parser_metaprogramming import (
    FilenameParseResult,
    MissingFilenameComponentError,
)
from openhcs.core.source_image_provenance import (
    SourceComponentMetadata,
    SourceImageIdentity,
    SourceImageProvenanceIdentity,
)
from openhcs.core.source_metadata import SourceMetadataFields
from openhcs.core.source_matching import (
    source_component_metadata_items,
)
from openhcs.core.source_projection import OpenHCSPlaneAddress
from openhcs.core.dataset_sources.interfaces import FilenameParser
from openhcs.core.axes import Axis, AxisFamily

ParsedFilenameValue: TypeAlias = str | int | float | bool | None
FunctionOutputComponentValue: TypeAlias = str | int
FunctionOutputComponentValues: TypeAlias = Mapping[str, FunctionOutputComponentValue]


class IncompleteFunctionOutputFilenameIdentityError(ValueError):
    """A parser-backed output identity lacks one required source component."""

    def __init__(self, component_name: str, message: str):
        self.component_name = component_name
        super().__init__(message)


@dataclass(frozen=True, slots=True)
class FunctionOutputParsedPathIdentityCacheKey:
    """Context-local cache identity for parser-derived output identity."""

    parser_id: int
    path_name: str
    source: str


@dataclass(frozen=True, slots=True)
class FunctionOutputFilenameCacheKey:
    """Context-local cache identity for constructed output filenames."""

    parser_id: int
    component_values: tuple[tuple[str, FunctionOutputComponentValue], ...]
    extension: str | None
    filename_qualifier: str | None


@dataclass(frozen=True, slots=True)
class FunctionOutputMetadataIdentityCacheKey:
    """Context-local cache identity for payload-metadata-derived output identity."""

    parser_id: int
    source_provenance_identity: SourceImageProvenanceIdentity
    fallback_identity_path: str | None
    identity_components: tuple[str, ...]
    input_aligned_output: bool


@dataclass(slots=True)
class FunctionOutputIdentityCache:
    """Processing-context-local cache for output identity filename resolution."""

    parsed_path_identities: dict[
        FunctionOutputParsedPathIdentityCacheKey,
        "FunctionOutputIdentity | None",
    ] = field(default_factory=dict)
    filenames_by_identity: dict[
        FunctionOutputFilenameCacheKey,
        str,
    ] = field(default_factory=dict)
    metadata_identities: dict[
        FunctionOutputMetadataIdentityCacheKey,
        "FunctionOutputIdentity | None",
    ] = field(default_factory=dict)


@dataclass(frozen=True, slots=True)
class FunctionOutputPathRequest:
    """Inputs needed to project one runtime output slice into a VFS path."""

    parser: FilenameParser
    output_dir: Path
    output_payload: RuntimeArrayData
    input_path: str | None
    variable_components: Sequence[type[Axis]] = field(default_factory=tuple)
    input_aligned_output: bool = False
    identity_cache: FunctionOutputIdentityCache = field(
        default_factory=FunctionOutputIdentityCache
    )


@dataclass(frozen=True, slots=True)
class FunctionOutputIdentity:
    """Semantic component identity used for one output filename."""

    component_values: FunctionOutputComponentValues
    extension: str | None
    source: str
    filename_component_values: FunctionOutputComponentValues | None = field(
        default=None,
        kw_only=True,
    )
    filename_qualifier: str | None = field(default=None, kw_only=True)

    @staticmethod
    def validate_output_paths(
        output_paths: Sequence[str],
        *,
        input_paths: Sequence[str],
        step_name: str,
        pattern_repr: str,
        identities: Sequence[FunctionOutputIdentity] = (),
    ) -> None:
        """Reject filename collisions before publishing a resolved output batch."""
        counts: dict[str, int] = {}
        for path in output_paths:
            counts[path] = counts.get(path, 0) + 1
        duplicates = tuple(path for path, count in counts.items() if count > 1)
        if not duplicates:
            return
        details = tuple(
            f"#{index}: input={input_paths[index] if index < len(input_paths) else None!r}, "
            f"output={output_paths[index]!r}, "
            f"identity={dict(identity.component_values)!r}, "
            f"filename_identity={dict(identity.filename_values)!r}, "
            f"source={identity.source!r}"
            for index, identity in enumerate(identities)
        )
        raise ValueError(
            f"Step {step_name!r} produced duplicate output path(s) "
            f"for pattern {pattern_repr}: {duplicates!r}. Input files: "
            f"{tuple(input_paths)!r}. Output identity details: {details!r}."
        )

    @property
    def filename_values(self) -> FunctionOutputComponentValues:
        """Storage coordinates, distinct from collapsed semantic components."""
        return (
            self.filename_component_values
            if self.filename_component_values is not None
            else self.component_values
        )

    @property
    def filename_address(self) -> OpenHCSPlaneAddress:
        """Project the retained producer coordinates without parsing its path."""
        return OpenHCSPlaneAddress.from_component_values(
            (component, self.filename_values.get(component.name))
            for component in AxisFamily.active().axes
        )

    def component_metadata(
        self,
        source_metadata: SourceComponentMetadata | None = None,
    ) -> SourceComponentMetadata:
        """Project semantic coordinates without rewriting acquisition file facts.

        The output's storage extension belongs to filename_component_metadata;
        it is not a new fact about the source carried by an image payload.
        """
        metadata = source_metadata if source_metadata is not None else {}
        return SourceMetadataFields.with_fields(
            SourceMetadataFields.composition_snapshot(metadata),
            self.component_values,
            components=source_component_metadata_items(self.component_values),
        )

    def filename_component_metadata(self) -> SourceComponentMetadata:
        """Return parser-compatible metadata used to construct the output filename."""
        metadata = dict(self.filename_values)
        if self.extension is not None:
            metadata["extension"] = self.extension
        return metadata

    def with_filename_qualifier(self, qualifier: str) -> "FunctionOutputIdentity":
        """Return this identity qualified by a declared output surface name."""
        return replace(
            self,
            filename_qualifier=self._normalize_filename_qualifier(qualifier),
        )

    def without_filename_qualifier(self) -> "FunctionOutputIdentity":
        """Return this identity without its output-surface filename qualifier."""
        return replace(self, filename_qualifier=None)

    _unsafe_qualifier_pattern: ClassVar[re.Pattern[str]] = re.compile(
        r"[^A-Za-z0-9_.-]+"
    )

    @classmethod
    def _normalize_filename_qualifier(cls, value: str) -> str:
        qualifier = cls._unsafe_qualifier_pattern.sub("_", str(value).strip())
        qualifier = qualifier.strip("_.-")
        if not qualifier:
            raise ValueError("Filename qualifier cannot be empty.")
        return qualifier

    def path_for_request(self, request: FunctionOutputPathRequest) -> Path:
        """Construct this identity's path in the request's output directory."""
        return Path(request.output_dir) / self.cached_filename(
            request.parser,
            request.identity_cache,
        )

    @classmethod
    def path_from_request(cls, request: FunctionOutputPathRequest) -> Path:
        """Resolve one runtime slice identity and construct its output path."""
        return cls.from_request(request).path_for_request(request)

    def cached_filename(
        self,
        parser: FilenameParser,
        identity_cache: FunctionOutputIdentityCache,
    ) -> str:
        cache_key = self._filename_cache_key(parser)
        cached = identity_cache.filenames_by_identity.get(cache_key)
        if cached is not None:
            return cached
        filename = self.filename(parser)
        identity_cache.filenames_by_identity[cache_key] = filename
        return filename

    def filename(self, parser: FilenameParser) -> str:
        """Construct this value's storage filename through the external parser."""
        component_values = dict(self.filename_values)
        extension = self.extension
        try:
            bound = parser.bind_component_values(component_values, extension=extension)
            filename = parser.construct_filename(bound)
            return self._qualified_filename(
                filename,
                self.filename_qualifier,
                extension=bound.extension,
            )
        except MissingFilenameComponentError as exc:
            raise IncompleteFunctionOutputFilenameIdentityError(
                exc.component_name,
                self._construction_error_message(component_values, extension),
            ) from exc
        except Exception as exc:
            raise ValueError(
                self._construction_error_message(component_values, extension),
            ) from exc

    def _construction_error_message(
        self,
        component_values: FunctionOutputComponentValues,
        extension: str | None,
    ) -> str:
        return (
            "Cannot construct FunctionStep output filename from "
            f"{self.source} identity. Components={component_values!r}, "
            f"extension={extension!r}."
        )

    @staticmethod
    def _qualified_filename(
        filename: str,
        qualifier: str | None,
        *,
        extension: str,
    ) -> str:
        if qualifier is None:
            return filename
        if not filename.endswith(extension):
            raise ValueError(
                "Constructed filename does not retain its declared extension."
            )
        return f"{filename[:-len(extension)]}_{qualifier}{extension}"

    def _filename_cache_key(
        self, parser: FilenameParser
    ) -> FunctionOutputFilenameCacheKey:
        return FunctionOutputFilenameCacheKey(
            parser_id=id(parser),
            component_values=tuple(
                sorted((str(key), value) for key, value in self.filename_values.items())
            ),
            extension=self.extension,
            filename_qualifier=self.filename_qualifier,
        )

    @classmethod
    def _first_extension(cls, *extensions: str | None) -> str | None:
        for extension in extensions:
            if extension is not None:
                return extension
        return None

    @classmethod
    def _extension_from_metadata(
        cls,
        metadata: SourceComponentMetadata | None,
    ) -> str | None:
        return cls._extension_from_raw(
            SourceImageIdentity(component_metadata=metadata).filename_extension
        )

    @classmethod
    def _extension_from_path(
        cls,
        path: str | None,
        *,
        parser: FilenameParser,
        identity_cache: FunctionOutputIdentityCache,
    ) -> str | None:
        if path is None:
            return None
        identity = cls._parsed_path_identity_with_cache(
            parser, path, source="source extension", identity_cache=identity_cache
        )
        if identity is not None:
            return identity.extension
        # Physical source paths need not have a canonical plane address. Their
        # terminal file suffix is not a chain of dotted source identity tokens.
        return cls._extension_from_raw(Path(path).suffix)

    @classmethod
    def _extension_from_source(
        cls,
        metadata: SourceComponentMetadata | None,
        path: str | None,
        *,
        parser: FilenameParser,
        identity_cache: FunctionOutputIdentityCache,
    ) -> str | None:
        """Honor retained extension declarations before external path decoding."""
        extension = cls._extension_from_metadata(metadata)
        if extension is not None:
            return extension
        return cls._extension_from_path(
            path, parser=parser, identity_cache=identity_cache
        )

    @staticmethod
    def _extension_from_raw(raw_extension: ParsedFilenameValue) -> str | None:
        if raw_extension is None:
            return None
        extension = str(raw_extension)
        if not extension:
            return None
        return extension

    @classmethod
    def _component_values_from_source_metadata(
        cls,
        metadata: SourceComponentMetadata | None,
    ) -> dict[str, FunctionOutputComponentValue]:
        if metadata is None:
            return {}
        return {
            component.name: SourceMetadataFields.canonical_component_value(
                component, value
            )
            for component, value in source_component_metadata_items(metadata)
        }

    @classmethod
    def component_values_from_parsed(
        cls,
        parsed: FilenameParseResult,
    ) -> dict[str, FunctionOutputComponentValue]:
        return {
            str(component.name): SourceMetadataFields.canonical_component_value(
                component, value
            )
            for component, value in parsed.declared_values()
            if value is not None
        }

    @classmethod
    def from_request(cls, request: FunctionOutputPathRequest) -> FunctionOutputIdentity:
        metadata = image_payload_metadata(request.output_payload)
        payload_identity = cls._identity_from_metadata_with_cache(
            request.parser,
            metadata,
            fallback_identity_path=request.input_path,
            variable_components=request.variable_components,
            input_aligned_output=request.input_aligned_output,
            identity_cache=request.identity_cache,
        )
        if payload_identity is not None:
            if payload_identity.extension is None:
                raise ValueError(
                    "FunctionStep output payload carries component identity but "
                    "no source path or extension. Refusing to borrow an input "
                    "extension for a semantic payload identity."
                )
            return cls._input_aligned_payload_identity(request, payload_identity)
        return cls._input_aligned_identity(request)

    @classmethod
    def from_metadata(
        cls,
        parser: FilenameParser,
        metadata: ImagePayloadMetadata,
        *,
        fallback_identity_path: str | None = None,
        variable_components: Sequence[type[Axis]] = (),
        input_aligned_output: bool = False,
    ) -> FunctionOutputIdentity | None:
        """Return parser-backed identity carried by image payload metadata."""
        return cls._identity_from_metadata_with_cache(
            parser,
            metadata,
            fallback_identity_path=fallback_identity_path,
            variable_components=variable_components,
            input_aligned_output=input_aligned_output,
            identity_cache=FunctionOutputIdentityCache(),
        )

    @classmethod
    def from_metadata_with_cache(
        cls,
        parser: FilenameParser,
        metadata: ImagePayloadMetadata,
        *,
        fallback_identity_path: str | None = None,
        variable_components: Sequence[type[Axis]] = (),
        input_aligned_output: bool = False,
        identity_cache: FunctionOutputIdentityCache,
    ) -> FunctionOutputIdentity | None:
        """Return parser-backed identity using a caller-owned identity cache."""
        return cls._identity_from_metadata_with_cache(
            parser,
            metadata,
            fallback_identity_path=fallback_identity_path,
            variable_components=variable_components,
            input_aligned_output=input_aligned_output,
            identity_cache=identity_cache,
        )

    @staticmethod
    def _source_stack_identity_component_values(
        variable_components: Sequence[type[Axis]],
    ) -> frozenset[str]:
        return frozenset(
            component.name
            for component in variable_components
            if component.name is not None
        )

    @classmethod
    def _identity_from_metadata_with_cache(
        cls,
        parser: FilenameParser,
        metadata: ImagePayloadMetadata,
        *,
        fallback_identity_path: str | None,
        variable_components: Sequence[type[Axis]],
        input_aligned_output: bool,
        identity_cache: FunctionOutputIdentityCache,
    ) -> FunctionOutputIdentity | None:
        """Return parser-backed identity using a caller-owned identity cache."""
        identity_component_values = cls._source_stack_identity_component_values(
            variable_components,
        )
        metadata_cache_key = FunctionOutputMetadataIdentityCacheKey(
            parser_id=id(parser),
            source_provenance_identity=metadata.source_provenance.equality_identity,
            fallback_identity_path=fallback_identity_path,
            identity_components=tuple(sorted(identity_component_values)),
            input_aligned_output=input_aligned_output,
        )
        if metadata_cache_key in identity_cache.metadata_identities:
            return identity_cache.metadata_identities[metadata_cache_key]
        identity = cls._identity_from_metadata_uncached(
            parser,
            metadata,
            fallback_identity_path=fallback_identity_path,
            identity_component_values=identity_component_values,
            input_aligned_output=input_aligned_output,
            identity_cache=identity_cache,
        )
        identity_cache.metadata_identities[metadata_cache_key] = identity
        return identity

    @classmethod
    def _identity_from_metadata_uncached(
        cls,
        parser: FilenameParser,
        metadata: ImagePayloadMetadata,
        *,
        fallback_identity_path: str | None,
        identity_component_values: frozenset[str],
        input_aligned_output: bool,
        identity_cache: FunctionOutputIdentityCache,
    ) -> FunctionOutputIdentity | None:
        """Resolve parser-backed identity without consulting the metadata cache."""
        represented_source_identities = (
            metadata.source_provenance.represented_source_identities
        )
        source_plane_count = metadata.source_provenance.source_plane_count
        if source_plane_count > 1:
            if identity_component_values:
                return cls._source_stack_identity_from_provenance(
                    parser,
                    metadata,
                    identity_component_values,
                    fallback_identity_path=fallback_identity_path,
                    input_aligned_output=input_aligned_output,
                    identity_cache=identity_cache,
                )
            if fallback_identity_path is not None:
                return None
            raise ValueError(
                "FunctionStep output slice carries multi-plane source "
                "provenance. Refusing to collapse multiple semantic identities "
                "into one output filename."
            )

        identity = cls._identity_from_metadata(
            metadata.source_component_metadata,
            extension=cls._extension_from_source(
                metadata.source_component_metadata,
                metadata.source_path,
                parser=parser,
                identity_cache=identity_cache,
            ),
            source="payload component metadata",
        )
        if identity is not None:
            if source_plane_count == 0 and len(represented_source_identities) > 1:
                filename_identity = cls.from_filename_metadata(
                    parser,
                    metadata,
                    fallback_identity_path=fallback_identity_path,
                )
                if filename_identity is None:
                    raise ValueError(
                        "Collapsed FunctionStep output provenance has no "
                        "parser-resolved filename identity."
                    )
                semantic_component_values = dict(identity.component_values)
                if not input_aligned_output:
                    for component_name in identity_component_values:
                        semantic_component_values.pop(component_name, None)
                return replace(
                    identity,
                    component_values=semantic_component_values,
                    extension=cls._first_extension(
                        identity.extension,
                        filename_identity.extension,
                    ),
                    filename_component_values=filename_identity.component_values,
                    source=(
                        f"{identity.source} with retained contributor filename "
                        "provenance"
                    ),
                )
            return cls._complete_identity_from_paths(
                parser,
                identity,
                (
                    (
                        metadata.source_path,
                        "payload source path",
                    ),
                    (
                        fallback_identity_path,
                        "fallback parsed filename",
                    ),
                ),
                identity_cache,
            )

        if len(represented_source_identities) == 1:
            source_identity = represented_source_identities[0]
            identity = cls._identity_from_metadata(
                source_identity.component_metadata,
                extension=cls._extension_from_source(
                    source_identity.component_metadata,
                    source_identity.path,
                    parser=parser,
                    identity_cache=identity_cache,
                ),
                source="single represented payload source metadata",
            )
            if identity is not None:
                return cls._complete_identity_from_paths(
                    parser,
                    identity,
                    (
                        (
                            source_identity.path,
                            "single represented payload source path",
                        ),
                        (
                            fallback_identity_path,
                            "fallback parsed filename",
                        ),
                    ),
                    identity_cache,
                )
            if source_identity.path is not None:
                return cls._parsed_path_identity_with_cache(
                    parser,
                    source_identity.path,
                    source="single represented payload source path",
                    identity_cache=identity_cache,
                )

        if metadata.source_path is not None:
            return cls._parsed_path_identity_with_cache(
                parser,
                metadata.source_path,
                source="payload source path",
                identity_cache=identity_cache,
            )
        return None

    @classmethod
    def from_filename_metadata(
        cls,
        parser: FilenameParser,
        metadata: ImagePayloadMetadata,
        *,
        fallback_identity_path: str | None = None,
    ) -> FunctionOutputIdentity | None:
        """Return the identity that should name a filename-addressed output."""
        identity_cache = FunctionOutputIdentityCache()
        represented_source_identities = (
            metadata.source_provenance.represented_source_identities
        )
        represented_source_path = (
            represented_source_identities[0].path
            if represented_source_identities
            else None
        )
        identity = cls._identity_from_metadata(
            metadata.source_component_metadata,
            extension=cls._extension_from_source(
                metadata.source_component_metadata,
                metadata.source_path,
                parser=parser,
                identity_cache=identity_cache,
            ),
            source="payload component metadata",
        )
        if identity is not None:
            return cls._complete_identity_from_paths(
                parser,
                identity,
                (
                    (
                        metadata.source_path,
                        "payload source path",
                    ),
                    (
                        represented_source_path,
                        "first represented payload source path",
                    ),
                    (
                        fallback_identity_path,
                        "fallback parsed filename",
                    ),
                ),
                identity_cache,
            )

        for path, source in (
            (
                metadata.source_path,
                "payload source path",
            ),
            (
                fallback_identity_path,
                "fallback parsed filename",
            ),
        ):
            if path is None:
                continue
            parsed_identity = cls._parsed_path_identity_with_cache(
                parser,
                path,
                source=source,
                identity_cache=identity_cache,
            )
            if parsed_identity is not None:
                return parsed_identity

        if represented_source_identities:
            return cls._source_stack_source_identity(
                parser,
                represented_source_identities[0],
                0,
                identity_cache,
            )
        return None

    @classmethod
    def _complete_identity_from_paths(
        cls,
        parser: FilenameParser,
        identity: FunctionOutputIdentity,
        candidates: tuple[tuple[str | None, str], ...],
        identity_cache: FunctionOutputIdentityCache,
    ) -> FunctionOutputIdentity:
        if identity.extension is not None and all(
            component.name in identity.component_values for component in AxisFamily.active().axes
        ):
            return identity
        for path, source in candidates:
            if path is None:
                continue
            parsed_identity = cls._parsed_path_identity_with_cache(
                parser,
                path,
                source=source,
                identity_cache=identity_cache,
            )
            if parsed_identity is None:
                continue
            component_values = dict(parsed_identity.component_values)
            component_values.update(identity.component_values)
            return FunctionOutputIdentity(
                component_values=component_values,
                extension=cls._first_extension(
                    identity.extension,
                    parsed_identity.extension,
                ),
                source=f"{identity.source} over {parsed_identity.source}",
            )
        return identity

    @classmethod
    def _parsed_path_identity_with_cache(
        cls,
        parser: FilenameParser,
        path: str,
        *,
        source: str,
        identity_cache: FunctionOutputIdentityCache,
    ) -> FunctionOutputIdentity | None:
        cache_key = FunctionOutputParsedPathIdentityCacheKey(
            parser_id=id(parser),
            path_name=source_path_identity(path).name,
            source=source,
        )
        if cache_key in identity_cache.parsed_path_identities:
            return identity_cache.parsed_path_identities[cache_key]
        identity = cls._parsed_path_identity(parser, path, source=source)
        identity_cache.parsed_path_identities[cache_key] = identity
        return identity

    @classmethod
    def _parsed_path_identity(
        cls,
        parser: FilenameParser,
        path: str,
        *,
        source: str,
    ) -> FunctionOutputIdentity | None:
        parsed = parser.parse_filename(source_path_identity(path).name)
        if parsed is None:
            return None
        return FunctionOutputIdentity(
            component_values=cls.component_values_from_parsed(parsed),
            extension=parsed.extension,
            source=source,
        )

    @classmethod
    def _source_stack_identity_from_provenance(
        cls,
        parser: FilenameParser,
        metadata: ImagePayloadMetadata,
        identity_component_values: frozenset[str],
        *,
        fallback_identity_path: str | None,
        input_aligned_output: bool,
        identity_cache: FunctionOutputIdentityCache,
    ) -> FunctionOutputIdentity:
        source_provenance = metadata.source_provenance
        semantic_source_identities = tuple(
            source_provenance.for_source_plane(plane_index).scalar_source_identity
            for plane_index in range(source_provenance.source_plane_count)
        )
        plane_identities = tuple(
            cls._source_stack_source_identity(
                parser,
                source_identity,
                identity_index,
                identity_cache,
            )
            for identity_index, source_identity in enumerate(semantic_source_identities)
        )
        semantic_component_values = cls._source_stack_semantic_component_values(
            plane_identities,
            identity_component_values,
            allow_non_identity_variation=input_aligned_output,
        )
        extension = cls._source_stack_extension(
            plane_identities,
            identity_component_values,
            fallback_identity_path=fallback_identity_path,
            parser=parser,
            identity_cache=identity_cache,
        )
        represented_source_identities = source_provenance.represented_source_identities
        if not represented_source_identities:
            raise ValueError(
                "FunctionStep output source stack has no represented source identity."
            )
        filename_identity = cls._source_stack_source_identity(
            parser,
            represented_source_identities[0],
            0,
            identity_cache,
        )
        filename_component_values = dict(filename_identity.component_values)
        return FunctionOutputIdentity(
            component_values=semantic_component_values,
            extension=extension,
            source=(
                "multi-plane payload provenance over identity components "
                f"{tuple(sorted(identity_component_values))!r}"
            ),
            filename_component_values=filename_component_values,
        )

    @classmethod
    def _source_stack_source_identity(
        cls,
        parser: FilenameParser,
        source_identity: SourceImageIdentity,
        identity_index: int,
        identity_cache: FunctionOutputIdentityCache,
    ) -> FunctionOutputIdentity:
        identity = cls._identity_from_metadata(
            source_identity.component_metadata,
            extension=cls._extension_from_source(
                source_identity.component_metadata,
                source_identity.path,
                parser=parser,
                identity_cache=identity_cache,
            ),
            source=f"represented source identity {identity_index} metadata",
        )
        if identity is not None:
            return cls._complete_identity_from_paths(
                parser,
                identity,
                (
                    (
                        source_identity.path,
                        f"represented source identity {identity_index} path",
                    ),
                ),
                identity_cache,
            )
        if source_identity.path is not None:
            parsed_identity = cls._parsed_path_identity_with_cache(
                parser,
                source_identity.path,
                source=f"represented source identity {identity_index} path",
                identity_cache=identity_cache,
            )
            if parsed_identity is not None:
                return parsed_identity
        raise ValueError(
            "FunctionStep output represented source has no parser-resolved "
            f"identity at index {identity_index}."
        )

    @classmethod
    def _source_stack_semantic_component_values(
        cls,
        plane_identities: tuple[FunctionOutputIdentity, ...],
        identity_component_values: frozenset[str],
        *,
        allow_non_identity_variation: bool = False,
    ) -> dict[str, FunctionOutputComponentValue]:
        semantic_keys = cls._source_stack_semantic_component_keys(
            plane_identities,
            identity_component_values,
        )
        semantic_component_values: dict[str, FunctionOutputComponentValue] = {}
        for key in semantic_keys:
            values = tuple(
                identity.component_values.get(key) for identity in plane_identities
            )
            if any(
                key not in identity.component_values for identity in plane_identities
            ):
                raise ValueError(
                    "FunctionStep output source stack provenance has inconsistent "
                    f"component coverage for non-stack component {key!r}."
                )
            if len(frozenset(values)) != 1:
                if allow_non_identity_variation:
                    continue
                raise ValueError(
                    "FunctionStep output source stack provenance varies outside "
                    "identity components. "
                    f"Component {key!r} has values {values!r}; identity components "
                    f"are {tuple(sorted(identity_component_values))!r}."
                )
            semantic_component_values[key] = values[0]
        return semantic_component_values

    @classmethod
    def _source_stack_semantic_component_keys(
        cls,
        plane_identities: tuple[FunctionOutputIdentity, ...],
        identity_component_values: frozenset[str],
    ) -> tuple[str, ...]:
        keys = (
            frozenset(
                key
                for identity in plane_identities
                for key in identity.component_values
            )
            - identity_component_values
        )
        ordered_keys = tuple(
            component.name for component in AxisFamily.active().axes if component.name in keys
        )
        extra_keys = tuple(sorted(keys - frozenset(ordered_keys)))
        return (*ordered_keys, *extra_keys)

    @classmethod
    def _source_stack_extension(
        cls,
        plane_identities: tuple[FunctionOutputIdentity, ...],
        identity_component_values: frozenset[str],
        *,
        fallback_identity_path: str | None,
        parser: FilenameParser,
        identity_cache: FunctionOutputIdentityCache,
    ) -> str | None:
        fallback_extension = cls._extension_from_path(
            fallback_identity_path, parser=parser, identity_cache=identity_cache
        )
        if fallback_extension is not None:
            return fallback_extension

        extensions = tuple(
            identity.extension
            for identity in plane_identities
            if identity.extension is not None
        )
        if not extensions:
            return None
        extension = extensions[0]
        if any(candidate != extension for candidate in extensions):
            raise ValueError(
                "FunctionStep output source stack provenance has multiple "
                f"extensions {extensions!r}; identity components are "
                f"{tuple(sorted(identity_component_values))!r}."
            )
        return extension

    @classmethod
    def _input_aligned_identity(
        cls,
        request: FunctionOutputPathRequest,
    ) -> FunctionOutputIdentity:
        if request.input_path is None:
            raise ValueError(
                "FunctionStep output payload has no component identity and no "
                "input path is available for input-aligned output identity."
            )
        parsed_identity = cls._parsed_path_identity_with_cache(
            request.parser,
            request.input_path,
            source="input-aligned parsed filename",
            identity_cache=request.identity_cache,
        )
        if parsed_identity is None:
            raise ValueError(
                "FunctionStep output payload has no component identity and the "
                f"input path cannot be parsed: {request.input_path!r}."
            )
        return parsed_identity

    @classmethod
    def _input_aligned_payload_identity(
        cls,
        request: FunctionOutputPathRequest,
        identity: FunctionOutputIdentity,
    ) -> FunctionOutputIdentity:
        """Complete unresolved payload identity from the aligned input filename."""
        if request.input_path is None:
            return identity
        parsed_identity = cls._parsed_path_identity_with_cache(
            request.parser,
            request.input_path,
            source="input-aligned parsed filename",
            identity_cache=request.identity_cache,
        )
        if parsed_identity is None:
            return identity
        split_component_values = cls._source_stack_identity_component_values(
            request.variable_components,
        )
        if identity.filename_component_values is not None:
            component_values = dict(identity.component_values)
            if request.input_aligned_output:
                # Alignment resolves this step's split axes, not coordinates
                # collapsed upstream and retained only in a storage filename.
                for component_name in (
                    split_component_values & parsed_identity.component_values.keys()
                ):
                    component_values.setdefault(
                        component_name,
                        parsed_identity.component_values[component_name],
                    )
            else:
                for component_name in split_component_values:
                    component_values.pop(component_name, None)
            filename_component_values = dict(parsed_identity.component_values)
            for (
                component_name,
                component_value,
            ) in identity.filename_component_values.items():
                if (
                    request.input_aligned_output
                    and component_name in split_component_values
                ):
                    continue
                filename_component_values[component_name] = component_value
            # Positional alignment fills unresolved storage coordinates; it
            # cannot rename a component already identified by the payload.
            filename_component_values.update(component_values)
            return replace(
                identity,
                component_values=component_values,
                extension=cls._first_extension(
                    identity.extension,
                    parsed_identity.extension,
                ),
                filename_component_values=filename_component_values,
            )

        component_values = dict(parsed_identity.component_values)
        component_values.update(identity.component_values)
        return replace(
            identity,
            component_values=component_values,
            extension=cls._first_extension(
                identity.extension,
                parsed_identity.extension,
            ),
            filename_component_values=dict(component_values),
        )

    @classmethod
    def _identity_from_metadata(
        cls,
        metadata: SourceComponentMetadata | None,
        *,
        extension: str | None,
        source: str,
    ) -> FunctionOutputIdentity | None:
        component_values = cls._component_values_from_source_metadata(metadata)
        if not component_values:
            return None
        return FunctionOutputIdentity(
            component_values=component_values,
            extension=extension,
            source=source,
        )
