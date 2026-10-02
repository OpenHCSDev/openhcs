"""Process-local projections of persisted custom-function declarations."""

from __future__ import annotations

import inspect
import threading
from collections.abc import Callable, Iterator, Mapping
from concurrent.futures import Future
from contextlib import contextmanager
from dataclasses import dataclass
from enum import Enum, auto
from typing import TYPE_CHECKING

from openhcs.constants import MemoryType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.function_contract_metadata import FunctionContractAttribute
from openhcs.processing.backends.lib_registry.unified_registry import FunctionMetadata
from openhcs.processing.custom_functions.source_namespace import (
    CustomFunctionSource,
    CustomFunctionSourceNamespace,
)

if TYPE_CHECKING:
    from .source_namespace import CustomFunctionSourceRevision


class CustomFunctionMetadata(FunctionMetadata):
    """Metadata whose lifetime is owned by the original custom-source registry."""

    def require_current_declaration(self) -> None:
        super().require_current_declaration()
        CustomFunctionRuntimeRegistry.require_current_metadata(self)


class CustomFunctionCanonicalLookup:
    """Independent source-lookup capability composed with the registry template."""

    @classmethod
    def _canonical_metadata_claims(
        cls, function_id: str, *, prepare_catalog: bool = True,
    ) -> Iterator[FunctionMetadata]:
        registry_name, _, name = function_id.partition(":")
        local = None
        if registry_name == cls._registry_name and name.isidentifier() and not name.startswith("_"):
            local = CustomFunctionRuntimeRegistry.metadata_for_name(name)
        if local is not None:
            yield local
        yield from super()._canonical_metadata_claims(
            function_id, prepare_catalog=prepare_catalog and local is None,
        )


class CustomFunctionLifetime(Enum):
    """Lifetime owned by one process-local custom-function declaration."""

    PERSISTED = auto()
    EPHEMERAL = auto()

    def require_current_source(self, source: CustomFunctionSource) -> None:
        """Validate the durable source only for the lifetime that owns a file."""
        if self is CustomFunctionLifetime.PERSISTED:
            from openhcs.processing.custom_functions.manager import (
                CustomFunctionManager,
            )

            CustomFunctionManager(create_storage=False).require_source(source)

    @classmethod
    def from_persist(cls, persist: bool) -> CustomFunctionLifetime:
        return cls.PERSISTED if persist else cls.EPHEMERAL


@dataclass(frozen=True, slots=True)
class CustomFunctionRuntimeDeclaration:
    """One projected custom function together with its source lifetime."""

    metadata: FunctionMetadata
    lifetime: CustomFunctionLifetime

    def require_source_namespace(
        self,
        namespace: CustomFunctionSourceNamespace,
    ) -> None:
        """Require this exact canonical namespace, with the declared source lifetime."""
        if vars(self.metadata.func).get(namespace.export_attribute) is not namespace:
            raise RuntimeError(
                "Custom source namespace changed; recompile the pipeline."
            )
        self.lifetime.require_current_source(namespace.source)


class CustomFunctionRuntimeRegistry:
    """Atomic process projection of custom-function declarations.

    This owner serializes source lifecycle operations with public-module and
    metadata publication.  Callers prepare declarations before entering the
    publication boundary; readers therefore observe either the old projection
    or the complete replacement, never a partially updated view.
    """

    _declarations_by_name: dict[str, CustomFunctionRuntimeDeclaration] = {}
    _published_exports: dict[str, Callable] = {}
    _preparation_outcomes: dict[CustomFunctionSource, Future[FunctionMetadata]] = {}
    _preparation_threads: dict[CustomFunctionSource, int] = {}
    _source_revision: CustomFunctionSourceRevision | None = None
    _lock = threading.RLock()

    @classmethod
    def _canonical_metadata_for_publication(
        cls,
        metadata: FunctionMetadata,
    ) -> FunctionMetadata:
        """Retain an exact source owner recreated after preparation selected it.

        Every caller holds the lifecycle lock through selection and publication.
        Unrevisioned declarations have no source-content identity to reselect.
        """
        revision = cls._declaration_revision(metadata)
        if revision is None:
            return metadata
        declaration = cls.declaration_for_source(
            CustomFunctionSource(metadata.original_name, revision)
        )
        return metadata if declaration is None else declaration.metadata

    @classmethod
    def declaration_for_source(
        cls,
        source: CustomFunctionSource,
    ) -> CustomFunctionRuntimeDeclaration | None:
        """Return the canonical declaration for this exact source, if published."""
        with cls._lock:
            declaration = cls._declarations_by_name.get(source.function_name)
            if declaration is None:
                return None
            if cls._declaration_revision(
                declaration.metadata
            ) != source.content_sha256 or not cls.owns_published_export(
                source.function_name
            ):
                return None
            return declaration

    @classmethod
    @contextmanager
    def lifecycle(cls):
        """Serialize one source mutation or lazy-load transaction."""

        with cls._lock:
            yield

    @classmethod
    def metadata_by_name(cls) -> Mapping[str, FunctionMetadata]:
        """Return a stable snapshot of the custom metadata view."""

        with cls._lock:
            return {
                name: declaration.metadata
                for name, declaration in cls._declarations_by_name.items()
            }

    @classmethod
    def metadata_for_name(cls, name: str) -> FunctionMetadata | None:
        """Load at most this source through the existing preparation/publication owner."""

        with cls._lock:
            declaration = cls._declarations_by_name.get(name)
            if declaration is not None:
                return declaration.metadata

        from openhcs.processing.custom_functions.manager import CustomFunctionManager

        CustomFunctionManager(create_storage=False).load_custom_function(
            name, clear_caches=False, publish_only_if_missing=True,
        )
        with cls._lock:
            declaration = cls._declarations_by_name.get(name)
            return None if declaration is None else declaration.metadata

    @classmethod
    def require_current_metadata(cls, metadata: FunctionMetadata) -> None:
        """Reject removed, replaced, displaced or changed-on-disk source claims."""

        with cls._lock:
            declaration = cls._declarations_by_name.get(metadata.original_name)
            if declaration is None or declaration.metadata is not metadata:
                raise RuntimeError("Custom function declaration changed; recompile the pipeline.")
            if not cls.owns_published_export(metadata.original_name):
                raise RuntimeError("Custom function public export changed; recompile the pipeline.")
            revision = cls._declaration_revision(metadata)
            if revision is not None:
                declaration.lifetime.require_current_source(
                    CustomFunctionSource(metadata.original_name, revision)
                )

    @classmethod
    def metadata_for_callable(cls, func: Callable) -> FunctionMetadata | None:
        """Return the exact custom metadata claim for one wrapper declaration."""

        declared = inspect.unwrap(func)
        with cls._lock:
            for declaration in cls._declarations_by_name.values():
                metadata = declaration.metadata
                if inspect.unwrap(metadata.func) is declared:
                    return metadata
        return None

    @classmethod
    def prepare_source_once(
        cls,
        source: CustomFunctionSource,
        factory: Callable[[], FunctionMetadata],
    ) -> FunctionMetadata:
        """Share one preparation outcome for one exact persisted source revision."""

        current_thread = threading.get_ident()
        with cls._lock:
            published = cls.declaration_for_source(source)
            if published is not None:
                return published.metadata
            for stale_key in tuple(cls._preparation_outcomes):
                if (
                    stale_key.function_name == source.function_name
                    and stale_key != source
                ):
                    cls._preparation_outcomes.pop(stale_key, None)
                    cls._preparation_threads.pop(stale_key, None)
            outcome = cls._preparation_outcomes.get(source)
            prepares = outcome is None
            if outcome is None:
                outcome = Future()
                cls._preparation_outcomes[source] = outcome
                cls._preparation_threads[source] = current_thread
            elif (
                not outcome.done()
                and cls._preparation_threads.get(source) == current_thread
            ):
                raise RuntimeError(
                    f"Recursive preparation of custom function {source.function_name!r} "
                    "for the same source revision is not supported."
                )

        if prepares:
            try:
                outcome.set_result(factory())
            except BaseException as exc:
                outcome.set_exception(exc)
            finally:
                with cls._lock:
                    cls._preparation_threads.pop(source, None)
        prepared = outcome.result()
        with cls._lock:
            published = cls.declaration_for_source(source)
            return prepared if published is None else published.metadata

    @classmethod
    def publish(
        cls,
        metadata: FunctionMetadata,
        lifetime: CustomFunctionLifetime,
    ) -> None:
        """Publish one prepared declaration with its exact source lifetime."""

        with cls._lock:
            metadata = cls._canonical_metadata_for_publication(metadata)
            cls._publish_locked(metadata, lifetime)
            if lifetime is CustomFunctionLifetime.PERSISTED:
                cls._source_revision = None

    @classmethod
    def ensure_can_publish(cls, metadata: FunctionMetadata) -> None:
        """Fail unless ``metadata`` may claim its public package export."""

        with cls._lock:
            cls._ensure_declaration_available_locked(metadata.original_name)
            cls._ensure_export_available_locked(metadata.original_name)

    @classmethod
    def ensure_can_replace(
        cls,
        old_name: str,
        metadata: FunctionMetadata,
    ) -> None:
        """Fail unless a replacement can retain or claim its package export."""

        with cls._lock:
            cls._ensure_declaration_available_locked(
                metadata.original_name,
                replacing_name=old_name,
            )
            cls._ensure_export_available_locked(
                metadata.original_name,
                replacing_name=old_name,
            )

    @classmethod
    def owns_published_export(cls, function_name: str) -> bool:
        """Return whether the runtime owns the exact current package export."""

        with cls._lock:
            published = cls._published_exports.get(function_name)
            if published is None:
                return False
            import openhcs.processing.custom_functions as custom_functions

            return vars(custom_functions).get(function_name) is published

    @classmethod
    def replace(cls, old_name: str, metadata: FunctionMetadata) -> None:
        """Atomically replace one runtime declaration, including a rename."""

        with cls._lock:
            metadata = cls._canonical_metadata_for_publication(metadata)
            new_name = metadata.original_name
            cls._ensure_export_available_locked(
                new_name,
                replacing_name=old_name,
            )
            cls._declarations_by_name.pop(old_name, None)
            if old_name != new_name:
                cls._remove_preparation_outcomes_locked(old_name)
                cls._remove_module_exports_locked((old_name,))
            cls._publish_locked(metadata, CustomFunctionLifetime.PERSISTED)
            cls._source_revision = None

    @classmethod
    def replace_all(
        cls,
        metadata_by_name: Mapping[str, FunctionMetadata],
        revision: CustomFunctionSourceRevision,
    ) -> None:
        """Replace persisted declarations while retaining ephemeral owners."""

        with cls._lock:
            metadata_by_name = {
                name: cls._canonical_metadata_for_publication(metadata)
                for name, metadata in metadata_by_name.items()
            }
            for function_name in metadata_by_name:
                cls._ensure_export_available_locked(function_name)
            ephemeral_declarations = {
                name: declaration
                for name, declaration in cls._declarations_by_name.items()
                if declaration.lifetime is CustomFunctionLifetime.EPHEMERAL
            }
            for function_name, metadata in metadata_by_name.items():
                ephemeral = ephemeral_declarations.get(function_name)
                if ephemeral is None:
                    continue
                if cls._declaration_revision(
                    ephemeral.metadata
                ) != cls._declaration_revision(metadata):
                    raise ValueError(
                        f"Persisted custom function {function_name!r} conflicts with "
                        "an ephemeral declaration in this process."
                    )
                ephemeral_declarations.pop(function_name)

            previous_names = tuple(cls._declarations_by_name)
            persisted_names = {
                name
                for name, declaration in cls._declarations_by_name.items()
                if declaration.lifetime is CustomFunctionLifetime.PERSISTED
            }
            for function_name in persisted_names - metadata_by_name.keys():
                cls._remove_preparation_outcomes_locked(function_name)
            cls._remove_module_exports_locked(previous_names)
            cls._declarations_by_name = {
                **ephemeral_declarations,
                **{
                    name: CustomFunctionRuntimeDeclaration(
                        metadata=metadata,
                        lifetime=CustomFunctionLifetime.PERSISTED,
                    )
                    for name, metadata in metadata_by_name.items()
                },
            }
            for declaration in cls._declarations_by_name.values():
                cls._publish_module_export_locked(declaration.metadata)
            cls._source_revision = revision

    @classmethod
    def remove(cls, function_name: str) -> None:
        """Remove one runtime projection and its public module export."""

        with cls._lock:
            declaration = cls._declarations_by_name.pop(function_name, None)
            cls._remove_preparation_outcomes_locked(function_name)
            cls._remove_module_exports_locked((function_name,))
            if (
                declaration is not None
                and declaration.lifetime is CustomFunctionLifetime.PERSISTED
            ):
                cls._source_revision = None

    @classmethod
    def clear(cls) -> None:
        """Clear every derived runtime projection and source revision."""

        with cls._lock:
            function_names = tuple(cls._declarations_by_name)
            cls._declarations_by_name.clear()
            cls._preparation_outcomes.clear()
            cls._preparation_threads.clear()
            cls._source_revision = None
            cls._remove_module_exports_locked(function_names)

    @classmethod
    def source_revision(cls) -> CustomFunctionSourceRevision | None:
        """Return the persisted source revision projected into this process."""

        with cls._lock:
            return cls._source_revision

    @classmethod
    def _publish_locked(
        cls,
        metadata: FunctionMetadata,
        lifetime: CustomFunctionLifetime,
    ) -> None:
        existing = cls._declarations_by_name.get(metadata.original_name)
        replacing_name = (
            metadata.original_name
            if existing is not None and existing.metadata is metadata
            else None
        )
        cls._ensure_declaration_available_locked(
            metadata.original_name, replacing_name=replacing_name
        )
        cls._ensure_export_available_locked(metadata.original_name)
        cls._declarations_by_name[metadata.original_name] = (
            CustomFunctionRuntimeDeclaration(
                metadata=metadata,
                lifetime=lifetime,
            )
        )
        cls._publish_module_export_locked(metadata)

    @classmethod
    def _ensure_declaration_available_locked(
        cls,
        function_name: str,
        *,
        replacing_name: str | None = None,
    ) -> None:
        existing = cls._declarations_by_name.get(function_name)
        if existing is None or function_name == replacing_name:
            return
        raise ValueError(f"Custom function {function_name!r} already exists.")

    @staticmethod
    def _declaration_revision(metadata: FunctionMetadata) -> str | None:
        return vars(metadata.func).get(FunctionContractAttribute.declaration_revision)

    @classmethod
    def _remove_preparation_outcomes_locked(cls, function_name: str) -> None:
        """Forget source outcomes when their persisted declaration is removed."""

        for key in tuple(cls._preparation_outcomes):
            if key.function_name == function_name:
                cls._preparation_outcomes.pop(key, None)
                cls._preparation_threads.pop(key, None)

    @classmethod
    def _ensure_export_available_locked(
        cls,
        function_name: str,
        *,
        replacing_name: str | None = None,
    ) -> None:
        """Protect public attributes owned outside the custom runtime."""

        import openhcs.processing.custom_functions as custom_functions

        namespace = vars(custom_functions)
        if function_name not in namespace:
            return
        current = namespace[function_name]
        published = cls._published_exports.get(function_name)
        if published is not None and current is published:
            return
        if replacing_name == function_name:
            replacing = cls._declarations_by_name.get(replacing_name)
            if replacing is not None and current is replacing.metadata.func:
                return
        raise ValueError(
            f"Custom function {function_name!r} conflicts with existing public "
            "package export owned outside the custom-function runtime."
        )

    @classmethod
    def _publish_module_export_locked(cls, metadata: FunctionMetadata) -> None:
        import openhcs.processing.custom_functions as custom_functions

        setattr(custom_functions, metadata.original_name, metadata.func)
        cls._published_exports[metadata.original_name] = metadata.func

    @classmethod
    def _remove_module_exports_locked(cls, function_names: tuple[str, ...]) -> None:
        import openhcs.processing.custom_functions as custom_functions

        namespace = vars(custom_functions)
        for function_name in function_names:
            published = cls._published_exports.pop(function_name, None)
            if published is not None and namespace.get(function_name) is published:
                namespace.pop(function_name, None)


def project_custom_function(
    func: Callable,
    *,
    declaration_revision: str | None = None,
) -> FunctionMetadata:
    """Build one custom runtime projection without publishing mutable state."""

    from openhcs.processing.backends.lib_registry.openhcs_registry import (
        OpenHCSRegistry,
    )
    from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

    callable_contract = CallableContract.from_callable(func)
    for role, memory_type in (
        ("input", callable_contract.input_memory_type),
        ("output", callable_contract.output_memory_type),
        ("execution", callable_contract.execution_memory_type),
    ):
        if memory_type is None:
            continue
        try:
            MemoryType(memory_type)
        except ValueError as exc:
            raise ValueError(
                f"Invalid custom-function {role} memory type: {memory_type!r}"
            ) from exc

    processing_contract = callable_contract.processing_contract
    if not isinstance(processing_contract, ProcessingContract):
        processing_contract = ProcessingContract.FLEXIBLE
        vars(func)[FunctionContractAttribute.processing_contract] = processing_contract

    registry = OpenHCSRegistry()
    if declaration_revision is not None:
        vars(func)[FunctionContractAttribute.declaration_revision] = (
            declaration_revision
        )
    wrapped = registry.apply_contract_wrapper(func, processing_contract)
    if declaration_revision is not None:
        vars(wrapped)[FunctionContractAttribute.declaration_revision] = (
            declaration_revision
        )
    metadata = CustomFunctionMetadata(
        name=func.__name__,
        func=wrapped,
        contract=processing_contract,
        registry=registry,
        module=func.__module__ or "",
        doc=func.__doc__ or "",
        tags=["openhcs", "custom"],
        original_name=func.__name__,
        memory_type=callable_contract.input_memory_type,
    )
    return metadata


def register_custom_function(func: Callable) -> Callable:
    """Project and publish one validated custom declaration."""

    metadata = project_custom_function(func)
    CustomFunctionRuntimeRegistry.publish(
        metadata,
        CustomFunctionLifetime.EPHEMERAL,
    )
    return metadata.func
