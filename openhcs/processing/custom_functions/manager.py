"""
Custom function manager for lifecycle operations.

Manages registration, persistence, loading, and deletion of custom functions.
All custom functions are stored in ~/.local/share/openhcs/custom_functions/
and automatically loaded on startup.

Architecture:
    - Uses exec() to execute user code in controlled namespace
    - Validates functions before and after execution
    - Projects valid declarations through the custom runtime registry
    - Persists to disk as .py files
    - Emits Qt signals for UI updates
"""

from __future__ import annotations

import logging
import os
import tempfile
from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, Callable

from arraybridge import MemoryType

from openhcs.core.callable_contract import CallableContract
from openhcs.core.xdg_paths import get_data_file_path
from openhcs.processing.custom_functions.events import custom_function_changed
from openhcs.processing.custom_functions.runtime_registry import (
    CustomFunctionLifetime,
    PersistedLifetime,
    CustomFunctionRuntimeRegistry,
    project_custom_function,
)
from openhcs.processing.custom_functions.source_namespace import (
    CustomFunctionSource,
    CustomFunctionSourceNamespace,
    CustomFunctionSourceRevision,
    CustomFunctionSourceSnapshot,
)
from openhcs.processing.custom_functions.validation import (
    ValidationError,
    declaration_line,
    failing_source_line,
    validate_code,
    validate_function,
)

if TYPE_CHECKING:
    from openhcs.processing.backends.lib_registry.unified_registry import (
        FunctionMetadata,
    )

logger = logging.getLogger(__name__)


# The file name ``exec`` gives frames of a persisted source it runs.
_SOURCE_FILENAME = "<string>"


@dataclass(frozen=True)
class PersistedCustomFunction(ABC):
    """
    One persisted custom-function source as the manager lists it.

    Attributes:
        name: Name the source file gives the function
        file_path: Path to source .py file
    """

    name: str
    file_path: Path

    @property
    @abstractmethod
    def list_label(self) -> str:
        """The text a list of custom functions shows for this source."""

    @property
    @abstractmethod
    def backend_label(self) -> str:
        """The memory type or scope, or why there is none."""

    @property
    @abstractmethod
    def status(self) -> str:
        """Whether the source is loaded, and the error when it is not."""


@dataclass(frozen=True)
class CustomFunctionLoadFailure(PersistedCustomFunction):
    """
    A persisted source that could not be loaded.

    Attributes:
        error: What preparing or publishing the source raised
    """

    error: Exception

    @property
    def message(self) -> str:
        if isinstance(self.error, ValidationError):
            return self.error.message
        return f"{type(self.error).__name__}: {self.error}"

    @property
    def line_number(self) -> int:
        """Source line of the error, 0 when the error has none."""
        if isinstance(self.error, ValidationError):
            return self.error.line_number
        return 0

    @property
    def list_label(self) -> str:
        return f"{self.name} (failed to load)"

    @property
    def backend_label(self) -> str:
        return "failed to load"

    @property
    def status(self) -> str:
        return f"Failed to load: {self.describe()}"

    def describe(self) -> str:
        """File, line and error as one line of text."""
        location = self.file_path.name
        if self.line_number:
            location = f"{location}, line {self.line_number}"
        return f"{location}: {self.message}"


@dataclass(frozen=True)
class CustomFunctionInfo(PersistedCustomFunction):
    """
    A persisted source that loaded.

    Attributes:
        contract: Original callable contract, also owning scope and memory type
    """

    contract: CallableContract

    @property
    def list_label(self) -> str:
        return self.name

    @property
    def status(self) -> str:
        return "Loaded"

    @property
    def memory_type(self) -> str | None:
        return self.contract.input_memory_type

    @property
    def doc(self) -> str:
        return self.contract.func.__doc__ or ""

    @property
    def backend_label(self) -> str:
        return self.memory_type or self.contract.execution_scope.value


def load_each_source(
    snapshots: tuple[CustomFunctionSourceSnapshot, ...],
    storage_dir: Path,
    prepare: Callable[[CustomFunctionSourceSnapshot], "FunctionMetadata"],
) -> tuple[dict[str, "FunctionMetadata"], tuple[CustomFunctionLoadFailure, ...]]:
    """Load each persisted source on its own: what loaded, and what failed.

    User source can raise anything while it is prepared or checked for
    publication. Each failure becomes a listed ``CustomFunctionLoadFailure``,
    so one source cannot hide the others and none is dropped.
    """
    prepared: dict[str, "FunctionMetadata"] = {}
    failures: list[CustomFunctionLoadFailure] = []
    for snapshot in snapshots:
        name = snapshot.source.function_name
        try:
            metadata = prepare(snapshot)
            CustomFunctionRuntimeRegistry.ensure_can_publish_persisted(metadata)
        except Exception as error:
            failures.append(
                CustomFunctionLoadFailure(
                    name=name, file_path=storage_dir / snapshot.file_name, error=error
                )
            )
        else:
            prepared[name] = metadata
    return prepared, tuple(failures)


class CustomFunctionManager:
    """
    Manager for custom function lifecycle operations.

    Handles registration, persistence, loading, and deletion of user-defined
    custom functions. All operations emit signals to notify UI components.

    Attributes:
        storage_dir: Directory where custom functions are stored
    """

    def require_source(self, expected: CustomFunctionSource) -> None:
        """Reject a persisted declaration whose actual source bytes changed."""
        current = self._snapshot_source(
            self.source_path_for_name(self.storage_dir, expected.function_name)
        )
        if current is None or current.source != expected:
            raise RuntimeError(
                f"Custom function source {expected.function_name!r} changed; "
                "recompile the pipeline."
            )

    storage_subdirectory = "custom_functions"

    @classmethod
    def default_storage_directory(cls) -> Path:
        """Resolve the native store without creating or migrating any files."""
        return get_data_file_path(cls.storage_subdirectory, create=False)

    @staticmethod
    def source_path_for_name(storage_dir: Path, function_name: str) -> Path:
        """Own source naming for both admission and actual persistence."""
        if not function_name.isidentifier() or function_name.startswith("_"):
            raise ValidationError("Custom function name must be a public Python identifier.")
        return storage_dir / f"{function_name}.py"

    def __init__(self, *, create_storage: bool = True):
        """Initialize manager and create storage directory if needed."""
        self.storage_dir: Path = self.default_storage_directory()
        if create_storage and not self.storage_dir.exists():
            self.storage_dir.mkdir(parents=True, exist_ok=True)
            logger.info(f"Created custom functions directory: {self.storage_dir}")

    def register_from_code(
        self,
        code: str,
        persist: bool = True,
        *,
        clear_caches: bool = True,
        emit_signal: bool = True,
        expected_function_name: str | None = None,
        write_admission: Callable[[Path], Path] | None = None,
    ) -> list[Callable]:
        """
        Validate and register the single declaration owned by this source.

        Validates code before execution, executes in controlled namespace,
        extracts decorated functions, validates them, and projects their
        runtime metadata through the custom-function owner.

        Args:
            code: Python code containing function definitions with decorators
            persist: If True, save code to storage directory

        Returns:
            A one-item list containing the registered runtime callable

        Raises:
            ValidationError: If code validation fails
            ValueError: If no valid functions found
            RuntimeError: If function registration fails
        """
        if persist and write_admission is not None:
            if expected_function_name is None:
                raise ValueError("Write admission requires an explicit custom function name.")
            write_admission(self.storage_dir)
            write_admission(self.source_path_for_name(self.storage_dir, expected_function_name))
        metadata = self._prepare_source(code)
        if expected_function_name is not None and metadata.original_name != expected_function_name:
            raise ValidationError(
                f"Prepared declaration {metadata.original_name!r} does not match "
                f"admitted function {expected_function_name!r}."
            )
        lifetime = CustomFunctionLifetime.from_persist(persist)
        with CustomFunctionRuntimeRegistry.lifecycle():
            CustomFunctionRuntimeRegistry.ensure_can_publish(metadata)
            if persist:
                source_path = self.source_path_for_function(metadata.func)
                if write_admission is not None:
                    write_admission(self.storage_dir)
                    write_admission(source_path)
                self.storage_dir.mkdir(parents=True, exist_ok=True)
                if source_path.exists():
                    raise ValueError(
                        f"Custom function '{metadata.original_name}' already exists; "
                        "use update_custom_function() to replace it."
                    )
                self._save_function_code(metadata.original_name, code)
            CustomFunctionRuntimeRegistry.publish(metadata, lifetime)

        registered_functions = [metadata.func]
        contract = CallableContract.from_callable(metadata.func)
        logger.info(
            "Registered custom function: %s (%s -> %s)",
            metadata.original_name,
            contract.input_memory_type,
            contract.output_memory_type,
        )

        if clear_caches:
            self._clear_caches()

        if emit_signal:
            custom_function_changed.emit()

        return registered_functions

    def source_path_for_function(self, func: Callable) -> Path:
        """Return the persisted source path used for a registered function."""
        return self.source_path_for_name(self.storage_dir, func.__name__)

    def source_revision(self) -> CustomFunctionSourceRevision:
        """Return a content-derived revision of all persisted declarations."""

        sources = tuple(
            CustomFunctionSource(
                function_name=source_path.stem,
                content_sha256=CustomFunctionSource.content_digest(source_path.read_bytes()),
            )
            for source_path in sorted(self.storage_dir.glob("*.py"))
        )
        return CustomFunctionSourceRevision(sources=sources)

    def load_all_custom_functions(self) -> int:
        """
        Load every .py file in the storage directory, each on its own.

        The sources that load are published as one exact set. A source that
        fails is reported with its file, line and error and stays listed as
        failed to load; it does not stop the others.

        Returns:
            Number of functions successfully loaded
        """
        if not self.storage_dir.exists():
            return 0

        revision, snapshots = self._snapshot_all_sources()
        prepared, failures = load_each_source(
            snapshots, self.storage_dir, self._prepare_snapshot
        )
        with CustomFunctionRuntimeRegistry.lifecycle():
            if revision == CustomFunctionRuntimeRegistry.source_revision():
                return len(prepared)
            self._require_revision(revision)
            CustomFunctionRuntimeRegistry.replace_all(prepared, revision)

        for failure in failures:
            logger.error(
                "Custom function failed to load: %s",
                failure.describe(),
                exc_info=failure.error,
            )
        self._clear_caches()
        if prepared or failures:
            custom_function_changed.emit()
        logger.info(
            "Loaded %d persisted custom function(s); %d failed to load",
            len(prepared),
            len(failures),
        )
        return len(prepared)

    def load_custom_function(
        self,
        func_name: str,
        *,
        clear_caches: bool = True,
        emit_signal: bool = False,
        publish_only_if_missing: bool = False,
    ) -> int:
        """
        Load one persisted custom function by name.

        Args:
            func_name: Name of the persisted custom function.
            clear_caches: Whether to clear function metadata caches after loading.
            emit_signal: Whether to emit the custom-functions-changed signal.
            publish_only_if_missing: Reuse an exact export published by a
                concurrent lazy loader instead of replacing its identity.

        Returns:
            Number of functions registered from the persisted file.
        """
        file_path = self.source_path_for_name(self.storage_dir, func_name)
        snapshot = self._snapshot_source(file_path)
        if snapshot is None:
            return 0

        metadata = self._prepare_snapshot(snapshot)

        with CustomFunctionRuntimeRegistry.lifecycle():
            self._require_snapshot(file_path, snapshot)
            if (
                publish_only_if_missing
                and CustomFunctionRuntimeRegistry.owns_published_export(func_name)
            ):
                return 1
            CustomFunctionRuntimeRegistry.publish(
                metadata,
                PersistedLifetime,
            )

        functions = [metadata.func]
        if clear_caches:
            self._clear_caches()
        if emit_signal:
            custom_function_changed.emit()
        logger.info(
            "Loaded %d custom function(s) from %s",
            len(functions),
            file_path.name,
        )
        return len(functions)

    def delete_custom_function(self, func_name: str) -> bool:
        """
        Remove function from registry and delete source file.

        The process-local runtime projection is removed with the persisted source.

        Args:
            func_name: Name of function to delete

        Returns:
            True if function file was deleted, False if not found
        """
        file_path = self.source_path_for_name(self.storage_dir, func_name)

        with CustomFunctionRuntimeRegistry.lifecycle():
            if not file_path.exists():
                logger.warning("Custom function file not found: %s", file_path)
                return False
            file_path.unlink()
            CustomFunctionRuntimeRegistry.remove(func_name)
        logger.info("Deleted custom function file: %s", file_path)

        # Clear caches
        self._clear_caches()

        # Emit signal
        custom_function_changed.emit()

        return True

    def list_custom_functions(self) -> list[PersistedCustomFunction]:
        """
        Return every persisted source: the loaded functions and the load failures.

        A source is prepared once per content; listing does not run it again.

        Returns:
            One entry per source file, ordered by file name
        """
        _revision, snapshots = self._snapshot_all_sources()
        prepared, failures = load_each_source(
            snapshots, self.storage_dir, self._prepare_snapshot
        )
        loaded = [
            CustomFunctionInfo(
                name=name,
                file_path=self.storage_dir / f"{name}.py",
                contract=CallableContract.from_callable(metadata.func),
            )
            for name, metadata in prepared.items()
        ]
        return sorted([*loaded, *failures], key=lambda listed: listed.file_path)

    def load_failures(self) -> tuple[CustomFunctionLoadFailure, ...]:
        """Return the persisted sources that could not be loaded."""
        _revision, snapshots = self._snapshot_all_sources()
        return load_each_source(snapshots, self.storage_dir, self._prepare_snapshot)[1]

    def get_function_code(self, func_name: str) -> str:
        """
        Get source code for a custom function.

        Args:
            func_name: Name of function

        Returns:
            Python source code

        Raises:
            ValueError: If function file not found
        """
        file_path = self.source_path_for_name(self.storage_dir, func_name)

        if not file_path.exists():
            raise ValueError(f"Custom function '{func_name}' not found")

        return file_path.read_bytes().decode("utf-8")

    def update_custom_function(self, old_name: str, new_code: str) -> str:
        """
        Atomically update a custom function.

        Validates new code first. If valid, writes new file with temp name,
        renames temp to final location, then deletes old file if name changed.
        If any step fails, old function is preserved.

        Args:
            old_name: Name of existing function to replace
            new_code: New Python code

        Returns:
            Name of the new function (may differ if renamed)

        Raises:
            ValueError: If old function not found
            ValidationError: If new code is invalid
            OSError: If file operations fail
        """
        old_file_path = self.source_path_for_name(self.storage_dir, old_name)
        old_snapshot = self._snapshot_source(old_file_path)
        if old_snapshot is None:
            raise ValueError(f"Custom function '{old_name}' not found")

        if new_code.encode("utf-8") == old_snapshot.content:
            metadata = CustomFunctionRuntimeRegistry.prepare_source_once(
                old_snapshot.source, lambda: self._prepare_source(new_code)
            )
        else:
            metadata = self._prepare_source(new_code)
        new_name = metadata.original_name
        new_file_path = self.source_path_for_name(self.storage_dir, new_name)
        temp_path = self._write_temporary_source(new_code)
        try:
            with CustomFunctionRuntimeRegistry.lifecycle():
                self._require_snapshot(old_file_path, old_snapshot)
                runtime_names = CustomFunctionRuntimeRegistry.metadata_by_name()
                if new_name != old_name and (
                    new_file_path.exists() or new_name in runtime_names
                ):
                    raise ValueError(
                        f"Custom function '{new_name}' already exists; rename aborted."
                    )
                CustomFunctionRuntimeRegistry.ensure_can_replace(old_name, metadata)

                os.replace(temp_path, new_file_path)
                if new_name != old_name:
                    try:
                        old_file_path.unlink()
                    except OSError:
                        new_file_path.unlink(missing_ok=True)
                        raise
                CustomFunctionRuntimeRegistry.replace(old_name, metadata)
        finally:
            temp_path.unlink(missing_ok=True)

        self._clear_caches()
        custom_function_changed.emit()
        return new_name

    def _create_execution_namespace(self) -> dict[str, object]:
        """
        Create controlled namespace for exec().

        The values are ``object`` because user code binds whatever it defines.

        Includes all memory type decorators and common imports.
        Does not restrict builtins (custom functions need full Python).

        Returns:
            Namespace dict for exec()
        """
        from openhcs.core.memory import decorators

        return {
            "__name__": "openhcs.processing.custom_functions",
            **{
                memory_type.value: getattr(decorators, memory_type.value)
                for memory_type in MemoryType
            },
        }

    def _prepare_source(
        self,
        code: str,
    ) -> "FunctionMetadata":
        """Validate and project one source without mutating runtime or disk state."""

        from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry

        validation_result = validate_code(code)
        if not validation_result.is_valid:
            raise ValidationError.at_line(
                "Code validation failed:\n" + "\n".join(validation_result.errors),
                code,
                validation_result.line_number,
            )

        namespace = self._create_execution_namespace()
        try:
            exec(compile(code, _SOURCE_FILENAME, "exec"), namespace)
        except Exception as exc:
            raise ValidationError.at_line(
                f"Code execution failed: {exc}",
                code,
                failing_source_line(exc, _SOURCE_FILENAME),
            ) from exc

        declared_names = set(validation_result.function_names)
        declarations = [
            obj
            for name, obj in namespace.items()
            if name in declared_names and not name.startswith("_") and callable(obj)
        ]
        declarations = [
            declaration
            for declaration in declarations
            if OpenHCSRegistry.declared_callable_contract(declaration) is not None
        ]
        if len(declarations) != 1:
            raise ValidationError(
                "Each custom-function source must declare exactly one decorated "
                f"processing function; found {len(declarations)}."
            )

        declaration = declarations[0]
        self._check_name_collision(declaration.__name__)
        function_validation = validate_function(declaration)
        if not function_validation.is_valid:
            raise ValidationError.at_line(
                f"Function '{declaration.__name__}' validation failed:\n"
                + "\n".join(function_validation.errors),
                code,
                declaration_line(code, declaration.__name__),
            )
        source = CustomFunctionSource(
            function_name=declaration.__name__,
            content_sha256=CustomFunctionSource.content_digest(code.encode("utf-8")),
        )
        CustomFunctionSourceNamespace(source, namespace).bind(declaration)
        try:
            return project_custom_function(
                declaration,
                declaration_revision=source.content_sha256,
            )
        except ValueError as exc:
            raise ValidationError.at_line(
                f"Function '{declaration.__name__}' projection failed: {exc}",
                code,
                declaration_line(code, declaration.__name__),
            ) from exc

    def _prepare_snapshot(
        self,
        snapshot: CustomFunctionSourceSnapshot,
    ) -> "FunctionMetadata":
        """Prepare one persisted source once; its file name must be its function name."""
        metadata = CustomFunctionRuntimeRegistry.prepare_source_once(
            snapshot.source, lambda: self._prepare_source(snapshot.code)
        )
        snapshot.require_declared_name(metadata.original_name)
        return metadata

    def _check_name_collision(
        self,
        function_name: str,
    ) -> None:
        """Reject a claim already proven by the loaded canonical catalog."""

        from openhcs.processing.backends.lib_registry.registry_service import (
            RegistryService,
        )

        composite_key = f"openhcs:{function_name}"
        metadata = RegistryService.cached_metadata_snapshot().get(composite_key)
        if metadata is not None and "custom" not in metadata.tags:
            raise ValueError(
                f"Function name {function_name!r} collides with a canonical "
                "OpenHCS function. Please choose a different name."
            )

    def _save_function_code(self, func_name: str, code: str) -> None:
        """
        Save function code to storage directory.

        Args:
            func_name: Name of function (used as filename)
            code: Python source code
        """
        file_path = self.source_path_for_name(self.storage_dir, func_name)
        temp_path = self._write_temporary_source(code)
        try:
            os.replace(temp_path, file_path)
        finally:
            temp_path.unlink(missing_ok=True)
        logger.info(f"Saved custom function to: {file_path}")

    def _snapshot_source(
        self,
        source_path: Path,
    ) -> CustomFunctionSourceSnapshot | None:
        """Read one exact persisted source without executing it."""

        try:
            source_bytes = source_path.read_bytes()
        except FileNotFoundError:
            return None
        return CustomFunctionSourceSnapshot(
            source=CustomFunctionSource(
                function_name=source_path.stem,
                content_sha256=CustomFunctionSource.content_digest(source_bytes),
            ),
            content=source_bytes,
        )

    def _snapshot_all_sources(
        self,
    ) -> tuple[
        CustomFunctionSourceRevision,
        tuple[CustomFunctionSourceSnapshot, ...],
    ]:
        """Read the persisted source set that one reconciliation will prepare."""

        snapshots = []
        for source_path in sorted(self.storage_dir.glob("*.py")):
            snapshot = self._snapshot_source(source_path)
            if snapshot is None:
                raise ValidationError(
                    "Persisted custom-function sources changed while being read; "
                    "retry reconciliation."
                )
            snapshots.append(snapshot)
        revision = CustomFunctionSourceRevision(
            sources=tuple(snapshot.source for snapshot in snapshots)
        )
        return revision, tuple(snapshots)

    def _require_snapshot(
        self,
        source_path: Path,
        expected: CustomFunctionSourceSnapshot,
    ) -> None:
        """Fail loudly when one prepared source no longer owns the same bytes."""

        current = self._snapshot_source(source_path)
        if current is None or current.source != expected.source:
            raise ValidationError(
                f"Persisted custom function '{source_path.name}' changed during "
                "preparation; retry the lifecycle operation."
            )

    def _require_revision(self, expected: CustomFunctionSourceRevision) -> None:
        """Fail loudly unless the prepared persisted source set is still exact."""

        try:
            current = self.source_revision()
        except FileNotFoundError as exc:
            raise ValidationError(
                "Persisted custom-function sources changed during preparation; "
                "retry reconciliation."
            ) from exc
        if current != expected:
            raise ValidationError(
                "Persisted custom-function sources changed during preparation; "
                "retry reconciliation."
            )

    def _write_temporary_source(self, code: str) -> Path:
        """Write source beside its destination for an atomic replacement."""

        file_descriptor, raw_path = tempfile.mkstemp(
            suffix=".py",
            dir=self.storage_dir,
        )
        try:
            with os.fdopen(file_descriptor, "wb") as stream:  # the digested bytes
                stream.write(code.encode("utf-8"))
                stream.flush()
                os.fsync(stream.fileno())
        except BaseException:
            Path(raw_path).unlink(missing_ok=True)
            raise
        return Path(raw_path)

    def _clear_caches(self) -> None:
        """
        Clear function registry metadata caches.

        Required after registration to ensure UI sees new functions.
        """
        from openhcs.processing.backends.lib_registry.registry_service import (
            RegistryService,
        )

        # Clear RegistryService metadata cache
        RegistryService.clear_metadata_cache()
        logger.debug("Cleared RegistryService metadata cache")

        # Custom functions are process-local projections and are intentionally
        # not stored in the OpenHCSRegistry disk cache.
