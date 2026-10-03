"""Headless function registry projection for OpenHCS agents."""

from __future__ import annotations

import inspect
import re
from abc import ABC, abstractmethod
from collections.abc import Callable
from concurrent.futures import CancelledError
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from pyqt_reactive.services.help_document import HelpDocument
from pyqt_reactive.services.parameter_help_service import (
    dataclass_type_from_annotation,
    docstring_info_for_target,
)
from python_introspect import (
    UnifiedParameterAnalyzer,
    enum_import_path,
    enum_input_values,
    enum_member_names,
    parameter_exclusions,
)
from zmqruntime import OperationCancellation

import openhcs.processing.custom_functions.manager as custom_function_manager
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.functions import (
    DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
    CellProfilerArtifactBindingSummary,
    CellProfilerModuleDeclarationSummary,
    CustomFunctionRegistrationDestination,
    CustomFunctionRegistrationDestinationRequest,
    CustomFunctionRegistrationRequest,
    CustomFunctionRegistrationResult,
    FunctionArtifactSpec,
    FunctionCatalogEntry,
    FunctionCatalogPage,
    FunctionDetail,
    FunctionParameterSource,
    FunctionParameterSpec,
    FunctionRuntimeContractSummary,
    catalog_page,
)
from openhcs.agent.exceptions import AgentFacingErrorMixin
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.core.artifacts import (
    ArtifactInputPlan,
    ArtifactSpec,
    MeasurementsArtifactType,
    RelationshipsArtifactType,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.interop.cellprofiler.setting_names import setting_names
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.lib_registry.unified_registry import FunctionMetadata

if TYPE_CHECKING:
    from openhcs.core.function_reference import FunctionReference

MAX_FUNCTION_DETAIL_DOC_CHARS = 50000


class FunctionCatalogError(AgentFacingErrorMixin, ValueError):
    """Base class for function catalog failures intended for agents."""


class UnknownFunctionIdError(FunctionCatalogError):
    """Raised when an agent references a function id outside the registry."""

    agent_error_code = "unknown_function_id"
    agent_error_hint = "Call openhcs_search_functions with biology or method terms, then pass one returned function_id exactly."

    def __init__(self, function_id: str) -> None:
        self.function_id = function_id
        super().__init__(f"Unknown OpenHCS function_id: {function_id}")


class CatalogSearchRank(Enum):
    ALL_PASS = 0
    EXACT_NAME = 10
    PREFIX_NAME = 20
    NAME_CONTAINS = 30
    ID_CONTAINS = 40
    IMPORT_CONTAINS = 50
    TAG_CONTAINS = 60
    PARAMETER_CONTAINS = 70
    SUMMARY_CONTAINS = 80
    DOC_CONTAINS = 90
    NO_MATCH = 1000

    @property
    def matched(self) -> bool:
        return self is not CatalogSearchRank.NO_MATCH


class SignatureView(Enum):
    FULL = 10000
    COMPACT = 4

    @property
    def parameter_limit(self) -> int:
        return self.value

    @property
    def compact(self) -> bool:
        return self is SignatureView.COMPACT


class AgentFunctionSearchPolicy:
    """Search-only text policy for agent function catalog ranking."""

    stop_words = frozenset(
        {
            "a",
            "an",
            "and",
            "are",
            "can",
            "could",
            "do",
            "does",
            "for",
            "have",
            "how",
            "i",
            "in",
            "is",
            "maybe",
            "my",
            "of",
            "or",
            "please",
            "the",
            "to",
            "use",
            "using",
            "want",
            "what",
            "with",
        }
    )

    @classmethod
    def accepts_token(cls, token: str) -> bool:
        return token not in cls.stop_words

    @classmethod
    def token_variants(cls, token: str) -> tuple[str, ...]:
        variants = [token]
        if len(token) > 4 and token.endswith("ies"):
            variants.append(f"{token[:-3]}y")
        if len(token) > 3 and token.endswith("s"):
            variants.append(token[:-1])
        return tuple(dict.fromkeys(variants))


@dataclass(frozen=True, slots=True)
class CatalogFilterText:
    text: str = ""
    tokens: tuple[str, ...] = ()

    @classmethod
    def from_request(cls, value: str | None) -> "CatalogFilterText":
        if value is None:
            return cls.all_pass()
        return cls.from_text(value)

    @classmethod
    def all_pass(cls) -> "CatalogFilterText":
        return cls()

    @classmethod
    def from_text(cls, value: str) -> "CatalogFilterText":
        text = _normalized_search_text(value)
        tokens = []
        seen = set()
        for token in text.split():
            if not AgentFunctionSearchPolicy.accepts_token(token) or token in seen:
                continue
            tokens.append(token)
            seen.add(token)
        return cls(text, tuple(tokens))

    def accepts_library_or_tag(
        self,
        library: str,
        backend_tags: tuple[str, ...],
    ) -> bool:
        """Match the registry library or one declaration-owned backend tag."""

        if not self.text:
            return True
        return self.text in {
            _normalized_search_text(value) for value in (library, *backend_tags)
        }

    def search_rank(
        self, entry: FunctionCatalogEntry, metadata: FunctionMetadata
    ) -> CatalogSearchRank:
        return self.search_match(entry, metadata).rank

    def search_match(
        self,
        entry: FunctionCatalogEntry,
        metadata: FunctionMetadata,
        parameters: tuple[FunctionParameterSpec, ...] = (),
    ) -> "CatalogTextMatch":
        if not self.text:
            return CatalogTextMatch(CatalogSearchRank.ALL_PASS, 0)
        name_text = _normalized_search_text(entry.name)
        function_id_text = _normalized_search_text(entry.function_id)
        import_path_text = _normalized_search_text(entry.import_path)
        tag_text = _normalized_search_text(" ".join(entry.backend_tags))
        if name_text == self.text:
            return CatalogTextMatch(CatalogSearchRank.EXACT_NAME, 10000)
        if name_text.startswith(self.text):
            return CatalogTextMatch(CatalogSearchRank.PREFIX_NAME, 9000)
        matches = []
        for rank, value in (
            (CatalogSearchRank.NAME_CONTAINS, name_text),
            (CatalogSearchRank.ID_CONTAINS, function_id_text),
            (CatalogSearchRank.IMPORT_CONTAINS, import_path_text),
            (CatalogSearchRank.TAG_CONTAINS, tag_text),
            (
                CatalogSearchRank.PARAMETER_CONTAINS,
                _parameter_search_text(parameters),
            ),
            (CatalogSearchRank.SUMMARY_CONTAINS, entry.summary or ""),
            (
                CatalogSearchRank.DOC_CONTAINS,
                PARAMETER_DOCUMENTATION_POLICY.detail_doc(metadata.func, metadata.doc) or "",
            ),
        ):
            score = self._text_score(value)
            if score:
                matches.append(CatalogTextMatch(rank, score))
        if not matches:
            return CatalogTextMatch(CatalogSearchRank.NO_MATCH, 0)
        return min(matches, key=lambda match: (-match.score, match.rank.value))

    def _matches_text(self, value: str) -> bool:
        return self._text_score(value) > 0

    def _text_score(self, value: str) -> int:
        text = _normalized_search_text(value)
        if self.text in text:
            # An exact phrase in a concise declaration is stronger evidence than
            # the same phrase buried in a long imported docstring. This remains
            # backend-neutral and lets callable owners improve discovery by
            # documenting their purpose precisely.
            density_bonus = round(100 * len(self.tokens) / max(1, len(text.split())))
            return 1000 + len(self.tokens) + density_bonus
        matched_count = sum(
            (1 for token in self.tokens if self._token_matches_text(token, text))
        )
        if not matched_count:
            return 0
        score = matched_count * 10
        if matched_count == len(self.tokens):
            score += 250
        return score

    @classmethod
    def _token_matches_text(cls, token: str, text: str) -> bool:
        text_tokens = tuple(text.split())
        for variant in cls._token_variants(token):
            if variant in text_tokens:
                return True
            if len(variant) >= 5 and any(
                (variant in text_token for text_token in text_tokens)
            ):
                return True
        return False

    @staticmethod
    def _token_variants(token: str) -> tuple[str, ...]:
        return AgentFunctionSearchPolicy.token_variants(token)


@dataclass(frozen=True, slots=True)
class CatalogTextMatch:
    rank: CatalogSearchRank
    score: int

    @property
    def matched(self) -> bool:
        return self.rank.matched


class SummaryView(Enum):
    FULL = 10000
    COMPACT = 180

    @property
    def character_limit(self) -> int:
        return self.value

    @property
    def compact(self) -> bool:
        return self is SummaryView.COMPACT


@dataclass(frozen=True, slots=True)
class CatalogSearchCandidate:
    rank: CatalogSearchRank
    score: int
    entry: FunctionCatalogEntry

    @property
    def sort_key(self) -> tuple[int, int, str, str]:
        return (
            -self.score,
            self.rank.value,
            self.entry.name.casefold(),
            self.entry.function_id,
        )


@dataclass(frozen=True, slots=True)
class CatalogSearchProjection:
    """Reusable search projection derived from one registry metadata mapping."""

    metadata: FunctionMetadata
    entry: FunctionCatalogEntry
    parameters: tuple[FunctionParameterSpec, ...]


class ParameterDocumentationPolicy:
    """Nominal policy for exposing callable parameters to agents."""

    variadic_kinds = frozenset(
        {inspect.Parameter.VAR_POSITIONAL, inspect.Parameter.VAR_KEYWORD}
    )

    def detail_doc(
        self,
        func: Callable,
        metadata_doc: str | None,
        contract: CallableContract | None = None,
    ) -> str | None:
        """Project authored prose from the original semantic callable owner.

        Runtime decorators can document controls that a host declaration removes.
        Their copied prose is not the public contract. Added parameter help stays
        on the final signature's typed parameter projection; request bindings
        remain semantic boundaries rather than being unwrapped to implementations.
        """
        callable_contract = contract or CallableContract.from_callable(func)
        doc = inspect.getdoc(callable_contract.resolve_raw_runtime_callable())
        if doc is not None:
            return doc
        if metadata_doc is not None and metadata_doc.strip():
            return metadata_doc
        return None

    def summary(
        self,
        func: Callable,
        metadata_doc: str | None,
        view: SummaryView,
        contract: CallableContract | None = None,
    ) -> str | None:
        doc = self.detail_doc(func, metadata_doc, contract)
        if doc is None:
            return None
        for line in doc.splitlines():
            stripped = line.strip()
            if stripped:
                return _bounded_summary(stripped, view)
        return None

    def should_document(
        self,
        name: str,
        parameter: inspect.Parameter,
        *,
        skip_keyword_bag: bool = False,
        hidden_names: frozenset[str] = frozenset(),
    ) -> bool:
        if name in hidden_names:
            return False
        if skip_keyword_bag and name == "kwargs":
            return False
        return parameter.kind not in self.variadic_kinds

    def display_signature(
        self,
        func: Callable,
        display_name: str,
        view: SignatureView,
        contract: CallableContract | None = None,
    ) -> str:
        sig = inspect.signature(func)
        supplied_by = self.supplied_by(func, contract)
        hidden_names = parameter_exclusions(func)
        visible_parameters = tuple(
            (
                parameter.replace(annotation=inspect.Parameter.empty)
                for name, parameter in sig.parameters.items()
                if self.should_document(
                    name, parameter, skip_keyword_bag=True, hidden_names=hidden_names
                )
                and supplied_by.get(name) is FunctionParameterSource.AGENT
            )
        )
        if view.compact and len(visible_parameters) > view.parameter_limit:
            parameter_names = ", ".join(
                (
                    parameter.name
                    for parameter in visible_parameters[: view.parameter_limit]
                )
            )
            return f"{display_name}({parameter_names}, ...)"
        visible_signature = sig.replace(parameters=visible_parameters)
        return f"{display_name}{visible_signature}"

    def parameter_specs(
        self, func: Callable, contract: CallableContract | None = None
    ) -> tuple[FunctionParameterSpec, ...]:
        sig = inspect.signature(func)
        supplied_by = self.supplied_by(func, contract)
        authored_descriptions = docstring_info_for_target(func).parameters or {}
        analyzed_parameters = UnifiedParameterAnalyzer.analyze(func)
        specs = []
        for name, parameter in sig.parameters.items():
            if not self.should_document(name, parameter):
                continue
            supplier = supplied_by[name]
            specs.append(
                FunctionParameterSpec(
                    name=name,
                    annotation=_format_annotation(parameter.annotation),
                    default_repr=_format_default(parameter.default),
                    required=supplier is FunctionParameterSource.AGENT
                    and parameter.default is inspect.Parameter.empty,
                    supplied_by=supplier,
                    description=self.parameter_description(
                        authored_descriptions.get(name),
                        supplier,
                        annotation=(
                            analyzed_parameters[name].param_type
                            if name in analyzed_parameters
                            else parameter.annotation
                        ),
                    ),
                    enum_import_path=enum_import_path(parameter.annotation),
                    enum_members=enum_member_names(parameter.annotation),
                    enum_values=enum_input_values(parameter.annotation),
                )
            )
        return tuple(specs)

    def agent_parameter_names(
        self, func: Callable, contract: CallableContract | None = None
    ) -> tuple[str, ...]:
        from openhcs.core.invocation_artifacts import (
            PipelineInvocationContractProviderAuthority,
        )

        contract = contract or CallableContract.from_callable(func)
        sig = inspect.signature(func)
        supplied_by = self.supplied_by(func, contract)
        hidden_names = parameter_exclusions(func)
        ordinary = tuple(
            (
                name
                for name, parameter in sig.parameters.items()
                if self.should_document(name, parameter, hidden_names=hidden_names)
                and supplied_by[name] is FunctionParameterSource.AGENT
            )
        )
        runtime_names = (
            contract.runtime_owned_parameter_names
            | hidden_names
            | {contract.primary_input_parameter_name}
        )
        compile_only = tuple(
            name
            for name in PipelineInvocationContractProviderAuthority.compile_time_parameter_names(contract)
            if name not in runtime_names
        )
        return tuple(dict.fromkeys((*ordinary, *compile_only)))

    def supplied_by(
        self, func: Callable, contract: CallableContract | None = None
    ) -> dict[str, FunctionParameterSource]:
        sig = inspect.signature(func)
        callable_contract = contract or CallableContract.from_callable(func)
        hidden_names = parameter_exclusions(func)
        supplied_by = {
            name: FunctionParameterSource.AGENT
            for name, parameter in sig.parameters.items()
            if self.should_document(name, parameter)
        }
        for name in hidden_names:
            if name in supplied_by:
                supplied_by[name] = FunctionParameterSource.RUNTIME_PARAMETER
        primary_input_name = callable_contract.primary_input_parameter_name
        if primary_input_name in supplied_by:
            supplied_by[primary_input_name] = FunctionParameterSource.PRIMARY_INPUT
        for name in callable_contract.artifact_input_parameter_names:
            if name in supplied_by:
                supplied_by[name] = FunctionParameterSource.ARTIFACT_INPUT
        for name in callable_contract.runtime_bound_parameters:
            if name in supplied_by:
                supplied_by[name] = FunctionParameterSource.RUNTIME_PARAMETER
        runtime_context_parameter = callable_contract.runtime_context_parameter
        if runtime_context_parameter in supplied_by:
            supplied_by[runtime_context_parameter] = (
                FunctionParameterSource.RUNTIME_PARAMETER
            )
        runtime_adapter = callable_contract.runtime_adapter
        if (
            runtime_adapter is not None
            and runtime_adapter.parameter_name in supplied_by
        ):
            supplied_by[runtime_adapter.parameter_name] = (
                FunctionParameterSource.RUNTIME_ADAPTER
            )
        return supplied_by

    def parameter_description(
        self,
        authored_description: str | None,
        supplier: FunctionParameterSource,
        *,
        annotation: object = inspect.Parameter.empty,
    ) -> str | None:
        """Compose declaration-owned field help with callable/runtime prose."""
        declaration = dataclass_type_from_annotation(annotation)
        if declaration is not None:
            document = HelpDocument.from_docstring_info(
                docstring_info_for_target(declaration)
            ).bounded()
            authored_description = "\n\n".join(
                part for part in (authored_description, document.content) if part
            )
        runtime_description = supplier.runtime_description
        if authored_description and runtime_description:
            return f"{authored_description.rstrip()} {runtime_description}"
        return authored_description or runtime_description


PARAMETER_DOCUMENTATION_POLICY = ParameterDocumentationPolicy()


class FunctionCatalogServiceABC(ABC):
    """Callable-catalog authority consumed by agent authoring services."""

    def prepare(
        self,
        *,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> None:
        """Prepare the authoritative catalog through this service's transport."""

        self.catalog(
            compact_signatures=True,
            status_callback=status_callback,
            cancellation=cancellation,
        )

    @abstractmethod
    def register_custom_function(
        self,
        request: CustomFunctionRegistrationRequest,
    ) -> CustomFunctionRegistrationResult:
        """Register one custom declaration through this catalog authority."""

    @abstractmethod
    def search(
        self,
        *,
        query: str | None = None,
        library: str | None = None,
        limit: int = 50,
        compact_signatures: bool = False,
    ) -> FunctionCatalogPage:
        """Search the authoritative callable catalog."""

    @abstractmethod
    def catalog(
        self,
        *,
        compact_signatures: bool = False,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> FunctionCatalogPage:
        """Return the complete authoritative callable catalog."""

    @abstractmethod
    def get(
        self,
        function_id: str,
        *,
        max_doc_chars: int | None = DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
        compact_signature: bool = True,
    ) -> FunctionDetail:
        """Return one callable detail."""

    @abstractmethod
    def get_by_import_path(
        self,
        import_path: str,
        *,
        max_doc_chars: int | None = DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
        compact_signature: bool = True,
    ) -> FunctionDetail | None:
        """Return the callable detail owned by one import path, when present."""

    @abstractmethod
    def resolve(self, function_id: str) -> Callable:
        """Resolve one selected callable without materializing another catalog."""

    @abstractmethod
    def reference(self, function_id: str) -> "FunctionReference":
        """Return a compiler reference without importing the callable locally."""


class FunctionCatalogService(FunctionCatalogServiceABC):
    """Expose registered OpenHCS processing callables through stable IDs."""

    def prepare(
        self,
        *,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> None:
        """Prepare metadata in the owned registry child, including cached catalogs."""

        RegistryService.prepare_persistent_catalog(
            status_callback=status_callback,
            cancellation=cancellation,
        )
        self.prepare_projections(status_callback=status_callback, cancellation=cancellation)

    def projections_current(self) -> bool:
        """Derive readiness from the original registry and cached public views."""
        from openhcs.processing.custom_functions.runtime_registry import (
            CustomFunctionRuntimeRegistry,
        )

        if self._projection_metadata is None or any(
            (signature_view, SummaryView[signature_view.name]) not in self._projections
            for signature_view in SignatureView
        ):
            return False
        if self._projection_metadata != RegistryService.cached_metadata_snapshot():
            return False
        manager = custom_function_manager.CustomFunctionManager(create_storage=False)
        return manager.source_revision() == CustomFunctionRuntimeRegistry.source_revision()

    def prepare_projections(
        self,
        *,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> None:
        """Prepare both public views, without repeating native kernel warmup."""
        while True:
            for signature_view in SignatureView:
                if cancellation is not None and cancellation.requested():
                    raise CancelledError
                self.catalog(
                    compact_signatures=signature_view.compact,
                    status_callback=status_callback,
                    cancellation=cancellation,
                )
            if self.projections_current():
                return

    def __init__(self, path_policy: AgentPathPolicy | None = None) -> None:
        self._path_policy = path_policy or AgentPathPolicy.from_environment()
        self._projection_metadata: dict[str, FunctionMetadata] | None = None
        self._projections: dict[
            tuple[SignatureView, SummaryView],
            tuple[CatalogSearchProjection, ...],
        ] = {}

    def register_custom_function(
        self, request: CustomFunctionRegistrationRequest
    ) -> CustomFunctionRegistrationResult:
        request = request.admitted(request.admission_policy or self._path_policy)
        # Caller admission cannot enlarge this server's own policy.
        request.admitted(self._path_policy)
        server_identity = request.require_server_identity()
        manager = custom_function_manager.CustomFunctionManager(create_storage=False)
        if request.persist and manager.storage_dir.resolve(strict=False) != Path(request.storage_dir).resolve(strict=False):
            raise ValueError(
                f"Selected endpoint owns custom storage {manager.storage_dir}, "
                f"not requested {request.storage_dir}; no source was evaluated."
            )
        def admit_write(path: Path) -> Path:
            self._path_policy.assert_writable(path)
            return request.admission_policy.assert_writable(path)

        registered_functions = manager.register_from_code(
            request.source_code, persist=request.persist,
            expected_function_name=request.function_name,
            write_admission=admit_write,
        )
        function_ids = self.function_ids_for_callables(tuple(registered_functions))
        entries = tuple(
            (
                self.get(
                    function_id,
                    max_doc_chars=0,
                    compact_signature=request.compact_signature,
                ).entry
                for function_id in function_ids
            )
        )
        source_file_paths = (
            tuple(
                (
                    str(manager.source_path_for_function(registered_function))
                    for registered_function in registered_functions
                )
            )
            if request.persist
            else ()
        )
        return CustomFunctionRegistrationResult(
            schema_version=SCHEMA_VERSION,
            registered_count=len(entries),
            persisted=request.persist,
            storage_dir=str(manager.storage_dir),
            source_file_paths=source_file_paths,
            functions=entries,
            next_steps=tuple(
                (
                    f"Call openhcs_describe_function(function_id={function_id!r}), then use openhcs_add_function_step or draft-pipeline-step."
                    for function_id in function_ids
                )
            ),
            connection=request.connection,
            server_identity=server_identity,
        )

    def custom_function_registration_destination(
        self, request: CustomFunctionRegistrationDestinationRequest
    ) -> CustomFunctionRegistrationDestination:
        """Project the native store without construction, source execution or IO."""
        manager_type = custom_function_manager.CustomFunctionManager
        storage_dir = manager_type.default_storage_directory()
        return CustomFunctionRegistrationDestination(
            storage_dir=str(storage_dir),
            source_file_path=(
                str(manager_type.source_path_for_name(storage_dir, request.function_name))
                if request.function_name is not None else None
            ),
        )

    def search(
        self,
        *,
        query: str | None = None,
        library: str | None = None,
        limit: int = 50,
        compact_signatures: bool = False,
    ) -> FunctionCatalogPage:
        if limit < 1:
            raise ValueError("limit must be at least 1")
        catalog_entries, entries = self._matching_entries(
            query=query,
            library=library,
            compact_signatures=compact_signatures,
        )
        return catalog_page(
            items=entries[:limit],
            catalog_items=catalog_entries,
            total=len(entries),
            limit=limit,
            query=query,
            library=library,
        )

    def catalog(
        self,
        *,
        compact_signatures: bool = False,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> FunctionCatalogPage:
        """Return the complete authoritative registered-function catalog."""
        catalog_entries, entries = self._matching_entries(
            query=None,
            library=None,
            compact_signatures=compact_signatures,
            status_callback=status_callback,
            cancellation=cancellation,
        )
        return catalog_page(
            items=entries,
            catalog_items=catalog_entries,
            total=len(entries),
            limit=len(entries),
            query=None,
            library=None,
        )

    def _matching_entries(
        self,
        *,
        query: str | None,
        library: str | None,
        compact_signatures: bool,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> tuple[
        tuple[FunctionCatalogEntry, ...],
        tuple[FunctionCatalogEntry, ...],
    ]:
        """Return ranked entries selected from the authoritative registry."""
        query_filter = CatalogFilterText.from_request(query)
        library_filter = CatalogFilterText.from_request(library)
        signature_view = (
            SignatureView.COMPACT if compact_signatures else SignatureView.FULL
        )
        summary_view = SummaryView.COMPACT if compact_signatures else SummaryView.FULL
        metadata_by_id = self._all_metadata(
            status_callback=status_callback,
            cancellation=cancellation,
        )
        projections = self._search_projections(
            metadata_by_id,
            signature_view=signature_view,
            summary_view=summary_view,
            status_callback=status_callback,
            cancellation=cancellation,
        )
        candidates = []
        for projection in projections:
            entry = projection.entry
            if not library_filter.accepts_library_or_tag(
                entry.library,
                entry.backend_tags,
            ):
                continue
            match = query_filter.search_match(
                entry,
                projection.metadata,
                projection.parameters,
            )
            if not match.matched:
                continue
            candidates.append(CatalogSearchCandidate(match.rank, match.score, entry))
        matching_entries = tuple(
            (
                candidate.entry
                for candidate in sorted(
                    candidates, key=lambda candidate: candidate.sort_key
                )
            )
        )
        return tuple(projection.entry for projection in projections), matching_entries

    def _search_projections(
        self,
        metadata_by_id: dict[str, FunctionMetadata],
        *,
        signature_view: SignatureView,
        summary_view: SummaryView,
        status_callback: Callable[[str], None] | None,
        cancellation: OperationCancellation | None = None,
    ) -> tuple[CatalogSearchProjection, ...]:
        """Project a registry revision once and reuse it across text queries."""

        if metadata_by_id is not self._projection_metadata:
            self._projection_metadata = metadata_by_id
            self._projections.clear()
        cache_key = (signature_view, summary_view)
        cached = self._projections.get(cache_key)
        if cached is not None:
            return cached
        if status_callback is not None:
            status_callback("Projecting function metadata for the execution endpoint")
        projections = []
        for function_id, metadata in sorted(metadata_by_id.items()):
            if cancellation is not None and cancellation.requested():
                raise CancelledError
            contract = CallableContract.from_callable(metadata.func)
            projections.append(
                CatalogSearchProjection(
                    metadata=metadata,
                    entry=self._entry(
                        function_id,
                        metadata,
                        signature_view,
                        summary_view,
                        contract=contract,
                    ),
                    parameters=PARAMETER_DOCUMENTATION_POLICY.parameter_specs(
                        metadata.func,
                        contract,
                    ),
                )
            )
        projected = tuple(projections)
        self._projections[cache_key] = projected
        return projected

    def get(
        self,
        function_id: str,
        *,
        max_doc_chars: int | None = DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
        compact_signature: bool = True,
    ) -> FunctionDetail:
        metadata = self._metadata(function_id)
        func = metadata.func
        contract = CallableContract.from_callable(func)
        # Owner resolution completes any declaration-projected callable help
        # before this immutable detail snapshot is assembled.
        runtime_contract = _runtime_contract_summary(func, contract)
        doc = PARAMETER_DOCUMENTATION_POLICY.detail_doc(func, metadata.doc, contract)
        bounded_doc, doc_truncated, effective_max_doc_chars = _bounded_detail_doc(
            doc, max_doc_chars=max_doc_chars
        )
        return FunctionDetail(
            schema_version=SCHEMA_VERSION,
            entry=self._entry(
                function_id,
                metadata,
                signature_view=(
                    SignatureView.COMPACT if compact_signature else SignatureView.FULL
                ),
                summary_view=SummaryView.COMPACT,
                contract=contract,
            ),
            parameters=PARAMETER_DOCUMENTATION_POLICY.parameter_specs(func, contract),
            doc=bounded_doc,
            runtime_contract=runtime_contract,
            doc_truncated=doc_truncated,
            doc_chars=len(doc or ""),
            max_doc_chars=effective_max_doc_chars,
        )

    def get_by_import_path(
        self,
        import_path: str,
        *,
        max_doc_chars: int | None = DEFAULT_FUNCTION_DETAIL_DOC_CHARS,
        compact_signature: bool = True,
    ) -> FunctionDetail | None:
        requested_import_path = import_path.strip()
        if not requested_import_path:
            return None
        for function_id, metadata in sorted(self._all_metadata().items()):
            entry = self._entry(
                function_id,
                metadata,
                signature_view=(
                    SignatureView.COMPACT if compact_signature else SignatureView.FULL
                ),
                summary_view=SummaryView.COMPACT,
            )
            if requested_import_path in _import_path_candidates(entry, metadata):
                return self.get(
                    function_id,
                    max_doc_chars=max_doc_chars,
                    compact_signature=compact_signature,
                )
        return None

    def resolve(self, function_id: str) -> Callable:
        return self._metadata(function_id).func

    def reference(self, function_id: str) -> "FunctionReference":
        """Return the exact compiler reference owned by one catalog declaration."""

        from openhcs.core.function_reference import FunctionReferenceTransportAuthority

        return FunctionReferenceTransportAuthority.function_reference(
            self._metadata(function_id).func
        )

    def require_revision(self, revision: str) -> None:
        """Fail unless ``revision`` names current endpoint callable membership."""

        if revision != self.catalog(compact_signatures=True).revision:
            raise ValueError(
                "The execution server function catalog changed after it was read. "
                "Refresh the catalog before selecting a function."
            )

    def function_ids_for_callables(
        self, functions: tuple[Callable, ...]
    ) -> tuple[str, ...]:
        metadata_by_id = self._all_metadata()
        return tuple(
            (self._function_id_for_callable(func, metadata_by_id) for func in functions)
        )

    @classmethod
    def _function_id_for_callable(
        cls, func: Callable, metadata_by_id: dict[str, FunctionMetadata]
    ) -> str:
        identity_matches = tuple(
            (
                function_id
                for function_id, metadata in metadata_by_id.items()
                if metadata.func is func
            )
        )
        if len(identity_matches) == 1:
            return identity_matches[0]
        semantic_matches = tuple(
            (
                function_id
                for function_id, metadata in metadata_by_id.items()
                if cls._metadata_matches_callable(metadata, func)
            )
        )
        if len(semantic_matches) == 1:
            return semantic_matches[0]
        if not semantic_matches:
            raise UnknownFunctionIdError(func.__name__)
        raise ValueError(
            f"Registered callable {func.__module__}.{func.__name__} matched multiple function ids: {semantic_matches!r}"
        )

    @staticmethod
    def _metadata_matches_callable(metadata: FunctionMetadata, func: Callable) -> bool:
        if metadata.module != func.__module__:
            return False
        return metadata.name == func.__name__ or metadata.original_name == func.__name__

    def _all_metadata(
        self,
        *,
        status_callback: Callable[[str], None] | None = None,
        cancellation: OperationCancellation | None = None,
    ) -> dict[str, FunctionMetadata]:
        from openhcs.processing.func_registry import (
            synchronize_custom_function_sources,
        )

        synchronize_custom_function_sources()
        return RegistryService.get_all_functions_with_metadata(
            status_callback=status_callback,
            cancellation=cancellation,
        )

    def _metadata(self, function_id: str) -> FunctionMetadata:
        try:
            return self._all_metadata()[function_id]
        except KeyError as exc:
            raise UnknownFunctionIdError(function_id) from exc

    def _entry(
        self,
        function_id: str,
        metadata: FunctionMetadata,
        signature_view: SignatureView = SignatureView.FULL,
        summary_view: SummaryView = SummaryView.FULL,
        contract: CallableContract | None = None,
    ) -> FunctionCatalogEntry:
        name = _metadata_display_name(function_id, metadata)
        module = _metadata_module(metadata)
        library = metadata.get_registry_name()
        callable_contract = contract or CallableContract.from_callable(metadata.func)
        signature = PARAMETER_DOCUMENTATION_POLICY.display_signature(
            metadata.func, name, signature_view, callable_contract
        )
        summary = PARAMETER_DOCUMENTATION_POLICY.summary(
            metadata.func, metadata.doc, summary_view, callable_contract
        )
        tags = metadata.tags
        backend_tags: tuple[str, ...]
        if tags is None:
            backend_tags = ()
        else:
            backend_tags = tuple((str(tag) for tag in tags))
        return FunctionCatalogEntry(
            function_id=function_id,
            name=name,
            module=module,
            library=library,
            import_path=_import_path(module, name),
            signature=signature,
            summary=summary,
            backend_tags=backend_tags,
        )


def _format_annotation(annotation) -> str | None:
    if annotation is inspect.Parameter.empty:
        return None
    if isinstance(annotation, type):
        return annotation.__name__
    return str(annotation)


def _format_default(default) -> str | None:
    if default is inspect.Parameter.empty:
        return None
    if isinstance(default, Enum):
        return f"{type(default).__name__}.{default.name}"
    return repr(default)


def _bounded_summary(text: str, view: SummaryView) -> str:
    if not view.compact:
        return text
    if len(text) <= view.character_limit:
        return text
    return f"{text[: view.character_limit - 3].rstrip()}..."


def _import_path(module: str, name: str) -> str:
    if not module:
        return name
    return f"{module}.{name}"


def _import_path_candidates(
    entry: FunctionCatalogEntry, metadata: FunctionMetadata
) -> frozenset[str]:
    func = metadata.func
    return frozenset(
        (
            candidate
            for candidate in (
                entry.import_path,
                _import_path(func.__module__, func.__name__),
                _import_path(func.__module__, func.__qualname__),
                _import_path(entry.module, func.__name__),
                _import_path(entry.module, func.__qualname__),
            )
            if candidate
        )
    )


def _normalized_search_text(value: str) -> str:
    text = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", value.strip())
    text = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", text).casefold()
    for separator in ("_", "-", ".", ":"):
        text = text.replace(separator, " ")
    return " ".join(text.split())


def _parameter_search_text(
    parameters: tuple[FunctionParameterSpec, ...],
) -> str:
    """Project declaration-owned parameter vocabulary into catalog search."""

    values: list[str] = []
    for parameter in parameters:
        values.extend(
            value
            for value in (
                parameter.name,
                parameter.annotation,
                parameter.default_repr,
                parameter.description,
                parameter.enum_import_path,
                *parameter.enum_members,
                *parameter.enum_values,
            )
            if value
        )
    return " ".join(values)


def _metadata_display_name(function_id: str, metadata: FunctionMetadata) -> str:
    if metadata.display_name:
        return metadata.display_name
    return function_id.rsplit(":", 1)[-1]


def _metadata_module(metadata: FunctionMetadata) -> str:
    if metadata.module:
        return metadata.module
    return metadata.func.__module__


def _runtime_contract_summary(
    func: Callable, contract: CallableContract | None = None
) -> FunctionRuntimeContractSummary:
    contract = contract or CallableContract.from_callable(func)
    artifact_inputs = _artifact_specs(contract.artifact_inputs)
    artifact_outputs = _artifact_specs(contract.artifact_outputs)
    cellprofiler_module = _cellprofiler_module_summary(contract)
    callable_kind = (
        "cellprofiler_module" if cellprofiler_module is not None else "regular"
    )
    return FunctionRuntimeContractSummary(
        callable_kind=callable_kind,
        processing_contract=_enum_member_name(contract.processing_contract),
        declared_processing_contract=contract.declared_processing_contract,
        runtime_bound_parameters=contract.runtime_bound_parameters,
        required_variable_components=tuple(
            component.name for component in contract.required_variable_components
        ),
        artifact_inputs=artifact_inputs,
        artifact_outputs=artifact_outputs,
        cellprofiler_module=cellprofiler_module,
        source_binding_rule=_source_binding_rule(cellprofiler_module, contract),
        materialization_rule=_materialization_rule(cellprofiler_module, contract),
        measurement_rule=_measurement_rule(cellprofiler_module, contract),
        pattern_compatibility_rule=_pattern_compatibility_rule(cellprofiler_module),
    )


def _artifact_specs(specs) -> tuple[FunctionArtifactSpec, ...]:
    return tuple((_artifact_spec(spec) for spec in specs))


def _artifact_spec(spec: ArtifactSpec) -> FunctionArtifactSpec:
    return FunctionArtifactSpec(
        name=spec.name,
        kind=spec.artifact_type.value,
        required=spec.required,
        sidecar_role=None if spec.sidecar_role is None else spec.sidecar_role.value,
        materialization_uses_source_identity_filename=spec.materialization_uses_source_identity_filename(),
        viewer_streaming=spec.viewer_streaming,
    )


def _cellprofiler_module_summary(
    contract: CallableContract,
) -> CellProfilerModuleDeclarationSummary | None:
    module_type = _cellprofiler_module_type(contract)
    if module_type is None:
        return None
    return CellProfilerModuleDeclarationSummary(
        module_name=module_type.require_module_name(),
        declaration_class=f"{module_type.__module__}.{module_type.__qualname__}",
        validated=bool(module_type.validated),
        function_names=module_type.declared_function_names(),
        aliases=tuple(module_type.aliases),
        artifact_bindings=tuple(
            _cellprofiler_artifact_binding_summary(binding)
            for binding in module_type.declared_artifact_bindings()
        ),
    )


def _cellprofiler_artifact_binding_summary(
    binding,
) -> CellProfilerArtifactBindingSummary:
    plan_type = binding.require_artifact_plan_type()
    return CellProfilerArtifactBindingSummary(
        direction="input" if plan_type is ArtifactInputPlan else "output",
        kind=binding.require_artifact_type().require_value(),
        setting_names=setting_names(binding.setting_name),
        parameter_name=binding.require_parameter_name(),
        runtime_parameter_name=binding.runtime_parameter_name,
        repeated=binding.repeated,
    )


def _cellprofiler_module_type(contract: CallableContract):
    from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule

    return CellProfilerModule.for_callable_contract(contract)


def _source_binding_rule(
    cellprofiler_module: CellProfilerModuleDeclarationSummary | None,
    contract: CallableContract,
) -> str | None:
    if cellprofiler_module is not None:
        return "CellProfiler exact artifact names are resolved from the module declaration, concrete FunctionStep groups, and compile-time setting identities. Callable-level artifact arrays can therefore be empty before compilation; inspect the module artifact_bindings here and the compiled artifact plan for exact names. Author selectors in FunctionStep func kwargs using each binding's parameter_name; for repeated bindings, use a tuple of exact artifact names (a one-element tuple selects one producer). These compile-time selectors are consumed by the declaration, not passed to the callable. runtime_parameter_name is runtime-owned: do not pass labels or other runtime payloads as function kwargs. When multiple label producers are available, select the exact intended output name; omission remains ambiguous and fails closed."
    if contract.artifact_inputs:
        return "Artifact input bindings are resolved from canonical CallableContract artifact_inputs during compilation."
    return None


def _materialization_rule(
    cellprofiler_module: CellProfilerModuleDeclarationSummary | None,
    contract: CallableContract,
) -> str | None:
    if cellprofiler_module is not None:
        return "Concrete CellProfiler sidecars and materialized artifacts are derived from canonical callable artifact outputs and the runtime plan, not chosen by MCP."
    if contract.artifact_outputs:
        return "Artifact output materialization is derived from output artifact kinds and compile/runtime materialization policy."
    return None


def _measurement_rule(
    cellprofiler_module: CellProfilerModuleDeclarationSummary | None,
    contract: CallableContract,
) -> str | None:
    measurement_kinds = {MeasurementsArtifactType, RelationshipsArtifactType}
    if any(
        (
            spec.artifact_type in measurement_kinds
            for spec in (*contract.artifact_inputs, *contract.artifact_outputs)
        )
    ):
        return "Measurement and relationship rows are projected by the selected runtime plan and materialized as declared artifacts."
    if cellprofiler_module is not None:
        return "If this module emits measurements, row ownership and sharing are declaration/runtime-plan behavior rather than agent-authored wiring."
    return None


def _pattern_compatibility_rule(
    cellprofiler_module: CellProfilerModuleDeclarationSummary | None,
) -> str | None:
    dict_rule = "Dictionary keys are normalized group identities selected by group_by, may intentionally cover only a subset of available component values, and omit groups that should not be invoked; compilation rejects keys absent from the available component domain."
    if cellprofiler_module is None:
        return f"Regular OpenHCS callables may participate in standard FunctionStep callable, tuple, list, or dict patterns subject to compiler validation. {dict_rule}"
    return f"Generated CellProfiler lowering uses one CP module contract per FunctionStep by default. Do not mix multiple CP module callables in one generated step unless declarations and compile-time invocation contracts explicitly allow it. {dict_rule}"


def _enum_member_name(value: Enum | None) -> str | None:
    if value is None:
        return None
    return value.name


def _bounded_detail_doc(
    doc: str | None, *, max_doc_chars: int | None
) -> tuple[str | None, bool, int | None]:
    if doc is None:
        return (None, False, max_doc_chars)
    if max_doc_chars is None:
        return (doc, False, None)
    effective_max_doc_chars = max(0, min(max_doc_chars, MAX_FUNCTION_DETAIL_DOC_CHARS))
    if len(doc) <= effective_max_doc_chars:
        return (doc, False, effective_max_doc_chars)
    return (doc[:effective_max_doc_chars].rstrip(), True, effective_max_doc_chars)
