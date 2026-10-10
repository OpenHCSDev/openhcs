"""
Unified registry base class for external library function registration.

This module provides a common base class that eliminates ~70% of code duplication
across library registries (pyclesperanto, scikit-image, cupy, etc.) while enforcing
consistent behavior and making it impossible to skip dynamic testing or hardcode
function lists.

Key Benefits:
- Eliminates ~1000+ lines of duplicated code
- Enforces consistent testing and registration patterns
- Makes adding new libraries trivial (60-120 lines vs 350-400)
- Centralizes bug fixes and improvements
- Type-safe abstract interface prevents shortcuts

Architecture:
- LibraryRegistryBase: Abstract base class with common functionality
- Dimension error adapter factory for consistent error handling
- Integrated caching system using existing cache_utils.py patterns
"""

import hashlib
import importlib
import inspect
import json
import logging
import os
import time
from abc import ABC, abstractmethod
from collections.abc import Callable as CallableABC, Iterator
from dataclasses import dataclass, field
from enum import Enum
from functools import wraps
from pathlib import Path
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Mapping,
    Optional,
    Tuple,
    get_args,
    get_origin,
    get_type_hints,
)

from arraybridge import MemoryContractAttribute
from metaclass_registry import AutoRegisterMeta, LazyDiscoveryDict, RegistryConfig
from polystore import atomic_write_json
from python_introspect import (
    SignatureAnalyzer,
    is_union_type,
    resolve_annotated,
)

from openhcs.constants import MemoryType
from openhcs.core.processing_contracts import (
    ContractProbe,
    LibraryContractCall,
    ProcessingContract,
)
from openhcs.core.runtime_array_values import is_array_payload
from openhcs.core.runtime_output_matching import runtime_output_tuple
from openhcs.core.xdg_paths import get_cache_file_path

logger = logging.getLogger(__name__)


def _registry_runtime_parameter_exclusions(
    signature: inspect.Signature,
    parameter_names: tuple[str, ...],
) -> tuple[str, ...]:
    """Return registry-owned injected parameter names present in a signature."""
    return tuple(
        parameter_name
        for parameter_name in parameter_names
        if parameter_name in signature.parameters
    )


def _set_registry_runtime_parameter_exclusions(
    target: object,
    signature: inspect.Signature,
    parameter_names: tuple[str, ...],
    *,
    source: object | None = None,
) -> None:
    """Merge registry-owned injected parameter names into analysis exclusions."""
    from python_introspect import add_parameter_exclusions, parameter_exclusions

    source_exclusions = () if source is None else parameter_exclusions(source)
    add_parameter_exclusions(
        target,
        (
            *source_exclusions,
            *_registry_runtime_parameter_exclusions(signature, parameter_names),
        ),
    )


# Enums for OpenHCS principle compliance (replace magic strings)
class ModuleFilterComponents(Enum):
    """Components to filter out when generating tags from module paths."""

    BACKENDS = "backends"
    PROCESSING = "processing"
    OPENHCS = "openhcs"

    @classmethod
    def should_skip(cls, component: str) -> bool:
        """Check if component should be skipped in tag generation."""
        return any(component == item.value for item in cls)


@dataclass(frozen=True)
class FunctionMetadata:
    """Clean metadata with no library-specific leakage."""

    # Core fields only
    name: str
    func: Callable
    contract: type[ProcessingContract]
    registry: "LibraryRegistryBase"  # Reference to the registry that registered this function - REQUIRED
    module: str = ""
    doc: str = ""
    tags: List[str] = field(default_factory=list)
    original_name: str = ""  # Original function name for cache reconstruction
    memory_type: str | None = None

    @property
    def composite_key(self) -> str:
        """Return this function's registry-owned transport identity."""

        return f"{self.registry.library_name}:{self.name}"

    def require_current_declaration(self) -> None:
        """Validate declaration lifetimes specialized by metadata owners."""

    @property
    def display_name(self) -> str:
        """Human-readable function name for catalogs and selectors."""
        if self.original_name:
            return self.original_name
        return self.name

    @property
    def import_identity(self):
        """Return the registry-owned public import identity."""

        from openhcs.core.callable_contract import CallableImportIdentity

        declared = inspect.unwrap(self.func)
        return CallableImportIdentity(
            module_name=self.module or declared.__module__,
            function_name=self.original_name or declared.__name__,
        )

    def get_memory_type(self) -> str | None:
        """
        Get the actual memory type (backend), if the function consumes arrays.

        Returns the memory type recorded at metadata creation time, otherwise
        the registry-level memory type for older cache entries.

        Returns:
            Memory type string (e.g., "cupy", "numpy", "torch",
            "pyclesperanto"), or ``None`` for plate-scoped functions that do
            not consume image arrays.
        """
        if self.memory_type is not None:
            return self.memory_type
        return self.registry.get_memory_type()

    def get_registry_name(self) -> str:
        """
        Get the registry name that registered this function.

        Returns:
            Registry name string (e.g., "openhcs", "skimage", "cupy", "pyclesperanto")
        """
        return self.registry.library_name


class LibraryRegistryBase(ABC, metaclass=AutoRegisterMeta):
    """ABC for declared library registries.

    Catalog projection, cache identity and runtime contracts live on this owner.

    Registry auto-created and stored as LibraryRegistryBase.__registry__.
    Subclasses auto-register by setting _registry_name class attribute.
    """

    __registry_config__ = RegistryConfig(
        registry_dict=LazyDiscoveryDict(),
        key_attribute="_registry_name",
        skip_if_no_key=True,
        registry_name="library registry",
        discovery_package="openhcs.processing.backends.lib_registry",
        discovery_recursive=False,
    )

    _registry_name: Optional[str] = (
        None  # Override in subclasses (e.g., 'pyclesperanto', 'cupy')
    )

    # Common exclusions across all libraries
    COMMON_EXCLUSIONS = {
        "imread",
        "imsave",
        "load",
        "save",
        "read",
        "write",
        "show",
        "imshow",
        "plot",
        "display",
        "view",
        "visualize",
        "info",
        "help",
        "version",
        "test",
        "benchmark",
    }
    EXCLUSIONS = COMMON_EXCLUSIONS
    CACHE_FORMAT_VERSION = "1.2"

    # Abstract class attributes - each implementation must define these
    MODULES_TO_SCAN: List[str]
    MEMORY_TYPE: (
        str  # Memory type string value (e.g., "pyclesperanto", "cupy", "numpy")
    )
    FLOAT_DTYPE: Any  # Library-specific float32 type (np.float32, cp.float32, etc.)

    @classmethod
    def loaded_registry_types(cls) -> tuple[type["LibraryRegistryBase"], ...]:
        """Return registry owners already declared in this process."""

        return tuple(dict.values(cls.__registry__))

    @classmethod
    def supports_cpu_only(cls) -> bool:
        """Return whether this registry's declared memory type is CPU-safe."""

        return cls.MEMORY_TYPE in (None, MemoryType.NUMPY.value)

    def __init__(self, library_name: str):
        """
        Initialize registry for a specific library.

        Args:
            library_name: Name of the library (e.g., "pyclesperanto", "skimage")
        """
        self.library_name = library_name
        self._cache_path = get_cache_file_path(f"{library_name}_function_metadata.json")
        self._library_warmed = False
        self._function_metadata_cache: Optional[Dict[str, FunctionMetadata]] = None
        self._function_metadata_cache_signature: str | None = None

    # ===== ESSENTIAL ABC METHODS =====

    # ===== LIBRARY IDENTIFICATION =====
    @abstractmethod
    def get_library_version(self) -> str:
        """Get library version for cache validation."""
        pass

    @abstractmethod
    def is_library_available(self) -> bool:
        """Check if the library is available for import."""
        pass

    def is_available_for_catalog(self) -> bool:
        """Return whether this registry can participate in catalog discovery.

        Import presence alone is not sufficient for runtimes such as CUDA: an
        installed package can still be unusable when a catalog submodule's
        native libraries or device runtime are unavailable.  The registry
        declaration owns that proof so every catalog reader selects the same
        registry set.
        """

        if not self.is_library_available():
            return False
        self._ensure_library_warmed()
        self.get_modules_to_scan()
        return True

    # ===== FUNCTION DISCOVERY =====
    @abstractmethod
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover and return function metadata. Must be implemented by subclasses."""
        pass

    @classmethod
    def metadata_for_declared_callable(
        cls,
        func: Callable,
    ) -> FunctionMetadata | None:
        """Project one declaration without discovering the registry catalog.

        Registries whose declarations carry enough local metadata may override
        this hook. Runtime-tested libraries retain catalog discovery as their
        authority.
        """

        del func
        return None

    @classmethod
    def _canonical_metadata_claims(
        cls, function_id: str, *, prepare_catalog: bool = True,
    ) -> Iterator[FunctionMetadata]:
        """Supply catalog-owned claims; independent capabilities compose via super."""

        from .registry_service import RegistryService

        catalog = (
            RegistryService.get_all_functions_with_metadata()
            if prepare_catalog else RegistryService.cached_metadata_snapshot()
        )
        metadata = catalog.get(function_id)
        if metadata is not None:
            yield metadata

    def owns_module(self, module_name: str) -> bool:
        """Whether ``module_name`` lies inside this registry's declared modules."""

        return any(
            module_name == module_pattern
            or module_name.startswith(f"{module_pattern}.")
            for module_pattern in self.get_module_patterns()
        )

    def composite_keys_for_declared_callable(
        self,
        func: Callable,
    ) -> tuple[str, ...]:
        """Derive every catalog key owned by one importable declaration."""

        metadata = type(self).metadata_for_declared_callable(func)
        if metadata is not None:
            return (metadata.composite_key,)

        declared = inspect.unwrap(func)
        if not self.owns_module(declared.__module__):
            return ()

        module_names = (
            "main" if module_name == "" else module_name
            for module_name in self.MODULES_TO_SCAN
        )
        return tuple(
            dict.fromkeys(
                f"{self.library_name}:"
                f"{self._generate_function_name(declared.__name__, module_name)}"
                for module_name in module_names
            )
        )

    # ===== CONTRACT HANDLING =====
    def apply_contract_wrapper(
        self, func: Callable, contract: type[ProcessingContract]
    ) -> Callable:
        """Apply contract wrapper with nominal runtime parameter injection."""
        import inspect
        from functools import wraps

        from python_introspect import (
            Enableable,
            mark_enableable,
            set_signature_analysis_target,
        )

        from openhcs.core.callable_contract import (
            CallableContract,
            FunctionStepExecutionScope,
        )
        from openhcs.core.config import runtime_config_parameter

        callable_contract = CallableContract.from_callable(func)
        if callable_contract.execution_scope is FunctionStepExecutionScope.PLATE:
            original_sig = inspect.signature(func, eval_str=True)
            enabled_parameter = Enableable.parameter()
            parameters = list(original_sig.parameters.values())
            if enabled_parameter.name not in original_sig.parameters:
                insert_index = next(
                    (
                        index
                        for index, parameter in enumerate(parameters)
                        if parameter.kind is inspect.Parameter.VAR_KEYWORD
                    ),
                    len(parameters),
                )
                parameters.insert(insert_index, enabled_parameter)

            @wraps(func)
            def plate_wrapper(*args, **kwargs):
                return func(*args, **Enableable.without_parameter(kwargs))

            plate_wrapper.__signature__ = original_sig.replace(parameters=parameters)
            plate_wrapper.__annotations__ = inspect.get_annotations(
                func,
                eval_str=False,
            ).copy()
            plate_wrapper.__annotations__[enabled_parameter.name] = (
                enabled_parameter.annotation
            )
            set_signature_analysis_target(plate_wrapper, func)
            _set_registry_runtime_parameter_exclusions(
                plate_wrapper,
                plate_wrapper.__signature__,
                (),
                source=func,
            )
            from openhcs.core.callable_contract import attach_callable_contract_metadata

            attach_callable_contract_metadata(
                plate_wrapper,
                raw_processing_function=func,
            )
            mark_enableable(plate_wrapper, enabled_default=True)
            return plate_wrapper

        original_sig = inspect.signature(func, eval_str=True)
        allowed_semantic_control_names = (
            contract.injected_semantic_control_parameter_names()
        )
        semantic_control_names = {
            parameter_type.require_parameter_name()
            for parameter_type in ProcessingContract.semantic_control_parameter_types()
        }
        params_to_strip = semantic_control_names - allowed_semantic_control_names
        runtime_config_parameters: list[inspect.Parameter] = []
        public_original_parameters: list[inspect.Parameter] = []
        for parameter in original_sig.parameters.values():
            if parameter.name in params_to_strip:
                continue
            normalized_parameter = runtime_config_parameter(parameter)
            if normalized_parameter is None:
                public_original_parameters.append(parameter)
                continue
            normalized_parameter = normalized_parameter.replace(
                default=normalized_parameter.annotation(),
            )
            runtime_config_parameters.append(normalized_parameter)
            public_original_parameters.append(normalized_parameter)
        public_original_parameters = tuple(public_original_parameters)
        public_sig = original_sig.replace(parameters=public_original_parameters)
        param_names = {p.name for p in public_sig.parameters.values()}

        runtime_parameter_types = contract.injected_runtime_parameter_types()
        runtime_parameter_names = (
            *(parameter.name for parameter in runtime_config_parameters),
            *(
                parameter_type.require_parameter_name()
                for parameter_type in runtime_parameter_types
            ),
        )
        injected_signature_parameters = (
            Enableable.parameter(),
            *(
                parameter_type.parameter()
                for parameter_type in contract.injected_runtime_parameter_types()
            ),
        )

        # Filter out already-existing parameters and declaration-name collisions.
        params_to_add: list[inspect.Parameter] = []
        seen_param_names = set(param_names)
        for parameter in injected_signature_parameters:
            if parameter.name in seen_param_names:
                continue
            params_to_add.append(parameter)
            seen_param_names.add(parameter.name)

        # If nothing to inject, return original function
        if not params_to_add and not params_to_strip and public_sig == original_sig:
            # Still brand the callable as Enableable metadata.
            from openhcs.core.callable_contract import attach_callable_contract_metadata

            mark_enableable(func, enabled_default=True)
            attach_callable_contract_metadata(
                func,
                runtime_bound_parameters=runtime_parameter_types,
            )
            _set_registry_runtime_parameter_exclusions(
                func,
                inspect.signature(func),
                runtime_parameter_names,
            )
            return func

        # Build new parameter list (insert before **kwargs)
        new_params = list(public_sig.parameters.values())
        insert_index = next(
            (
                i
                for i, parameter in enumerate(new_params)
                if parameter.kind == inspect.Parameter.VAR_KEYWORD
            ),
            len(new_params),
        )

        for parameter in params_to_add:
            new_params.insert(insert_index, parameter)
            insert_index += 1

        # Create wrapper
        @wraps(func)
        def wrapper(image, *args, **kwargs):
            if params_to_strip:
                kwargs = {
                    name: value
                    for name, value in kwargs.items()
                    if name not in params_to_strip
                }

            # Populate missing wrapper controls with their defaults from the signature
            # This is critical for internal calls between OpenHCS functions where
            # wrapper controls may not be explicitly passed (e.g., create_projection calling max_projection)
            from python_introspect import SignatureAnalyzer

            sig_params = SignatureAnalyzer.analyze(wrapper)
            signature_parameters = (
                *runtime_config_parameters,
                *injected_signature_parameters,
            )
            for parameter in signature_parameters:
                param_name = parameter.name
                if param_name not in kwargs and param_name in sig_params:
                    default_value = sig_params[param_name].default_value
                    if default_value is not inspect.Parameter.empty:
                        kwargs[param_name] = default_value

            # Keep only declared controls that participate in execution.
            execution_parameter_names = (
                frozenset(parameter.name for parameter in runtime_config_parameters)
                | contract.execution_parameter_names()
            )
            params_to_filter = {
                parameter.name
                for parameter in signature_parameters
                if parameter.name not in execution_parameter_names
            }
            filtered_kwargs = {
                k: v for k, v in kwargs.items() if k not in params_to_filter
            }

            return contract.execute(
                LibraryContractCall(func, args), image, filtered_kwargs,
            )

        wrapper.__signature__ = public_sig.replace(parameters=new_params)
        wrapper.__annotations__ = inspect.get_annotations(func, eval_str=False).copy()
        for parameter in (
            *runtime_config_parameters,
            *injected_signature_parameters,
        ):
            wrapper.__annotations__[parameter.name] = parameter.annotation
        set_signature_analysis_target(wrapper, func)
        _set_registry_runtime_parameter_exclusions(
            wrapper,
            wrapper.__signature__,
            runtime_parameter_names,
            source=func,
        )

        # The registry wrapper owns the exact declared or runtime-classified contract.
        from openhcs.core.callable_contract import attach_callable_contract_metadata
        from openhcs.core.function_contract_metadata import FunctionContractAttribute

        processing_contract_key = FunctionContractAttribute.processing_contract
        vars(wrapper)[processing_contract_key] = contract
        attach_callable_contract_metadata(
            wrapper,
            raw_processing_function=func,
            runtime_bound_parameters=runtime_parameter_types,
        )

        # Nominal enable semantics: decorated callables are Enableable.
        # (Enableable is metadata only; enabled remains owned by python_introspect.)
        mark_enableable(wrapper, enabled_default=True)

        return wrapper

    def _get_function_by_name(self, module_path: str, func_name: str):
        """Get function object by module path and name."""
        module = importlib.import_module(module_path)
        try:
            return getattr(module, func_name)
        except AttributeError as exc:
            raise AttributeError(func_name) from exc

    def create_library_adapter(
        self,
        original_func: Callable,
        contract: type[ProcessingContract],
    ) -> Callable:
        """Return the callable shape used before contract wrapping."""
        return original_func

    def reconstruct_cached_callable(
        self,
        func: Callable,
        contract: type[ProcessingContract],
    ) -> Callable:
        """Reconstruct one cached callable through this registry's runtime policy."""

        adapted_func = self.create_library_adapter(func, contract)
        return self.apply_contract_wrapper(adapted_func, contract)

    # ===== LIBRARY WARM-UP HOOK =====
    def _warmup_library(self) -> None:
        """
        Optional hook for registries that need to pre-initialize their library.

        Subclasses can override to run lightweight imports or self-tests that
        ensure required shared libraries are available before discovery begins.
        """
        return

    def _ensure_library_warmed(self) -> None:
        """Ensure library warm-up hook is invoked exactly once."""
        if self._library_warmed:
            return

        try:
            self._warmup_library()
        except Exception as exc:
            logger.warning(f"{self.library_name} warm-up failed: {exc}")
            raise

        self._library_warmed = True

    # ===== CACHING METHODS =====
    def load_or_discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Load functions from cache or discover them if cache is invalid."""
        logger.info(f"🔄 load_or_discover_functions called for {self.library_name}")

        cached_functions = self.load_cached_functions()
        if cached_functions is not None:
            logger.info(
                f"✅ Loaded {len(cached_functions)} {self.library_name} functions from cache"
            )
            return cached_functions

        logger.info(
            f"🔍 Cache miss for {self.library_name} - performing full discovery"
        )
        functions = self.discover_functions()
        self._save_to_cache(functions)
        return self._remember_function_metadata(functions)

    def load_cached_functions(self) -> Optional[Dict[str, FunctionMetadata]]:
        """Load only a valid persistent catalog, without runtime discovery."""

        self._ensure_library_warmed()
        self._prepare_cached_function_inventory()
        discovery_signature = self.get_discovery_signature()
        if (
            self._function_metadata_cache is not None
            and self._function_metadata_cache_signature == discovery_signature
        ):
            return self._function_metadata_cache
        cached_functions = self._load_from_cache()
        if cached_functions is None:
            return None
        return self._remember_function_metadata(cached_functions)

    def _prepare_cached_function_inventory(self) -> None:
        """Prepare the module declaration used to validate cached functions."""

        self.get_modules_to_scan()

    def _remember_function_metadata(
        self,
        functions: Dict[str, FunctionMetadata],
    ) -> Dict[str, FunctionMetadata]:
        """Retain one discovery-signature-specific metadata projection."""

        self._function_metadata_cache = functions
        self._function_metadata_cache_signature = self.get_discovery_signature()
        return functions

    def _load_from_cache(self) -> Optional[Dict[str, FunctionMetadata]]:
        """Load function metadata from cache with validation."""
        cache_path = self.persistent_cache_path()
        logger.debug(f"📂 LOAD FROM CACHE: Checking cache for {self.library_name}")

        if not cache_path.exists():
            logger.debug(f"📂 LOAD FROM CACHE: No cache file exists at {cache_path}")
            return None

        try:
            with open(cache_path, "r") as f:
                cache_data = json.load(f)
        except json.JSONDecodeError:
            logger.warning(f"Corrupt cache file {cache_path}, rebuilding")
            return None

        if "functions" not in cache_data:
            return None

        if cache_data.get("cache_version") != self.CACHE_FORMAT_VERSION:
            logger.info(
                "%s function cache format changed - cache invalid",
                self.library_name,
            )
            return None

        cached_version = cache_data.get("library_version", "unknown")
        current_version = self.get_library_version()
        if cached_version != current_version:
            logger.info(
                f"{self.library_name} version changed ({cached_version} → {current_version}) - cache invalid"
            )
            return None

        cached_signature = cache_data.get("discovery_signature")
        current_signature = self.get_discovery_signature()
        if cached_signature != current_signature:
            logger.info(f"{self.library_name} discovery inputs changed - cache invalid")
            return None

        cache_timestamp = cache_data.get("timestamp", 0)
        cache_age_days = (time.time() - cache_timestamp) / (24 * 3600)
        if cache_age_days > 7:
            logger.debug(f"Cache is {cache_age_days:.1f} days old - rebuilding")
            return None

        logger.debug(
            f"📂 LOAD FROM CACHE: Loading {len(cache_data['functions'])} functions for {self.library_name}"
        )

        functions = {}
        for func_name, cached_data in cache_data["functions"].items():
            original_name = cached_data.get("original_name", func_name)
            try:
                func = self._get_function_by_name(
                    cached_data["module"],
                    original_name,
                )
            except (AttributeError, ImportError, ModuleNotFoundError) as exc:
                logger.warning(
                    "Registry cache entry %s is stale for %s; rebuilding %s cache: %s",
                    func_name,
                    self.library_name,
                    self.library_name,
                    exc,
                )
                return None
            if not callable(func):
                logger.warning(
                    "Registry cache entry %s for %s resolved to non-callable %r; "
                    "rebuilding %s cache",
                    func_name,
                    self.library_name,
                    type(func).__name__,
                    self.library_name,
                )
                return None
            contract = ProcessingContract.for_key(cached_data["contract"])

            final_func = self.reconstruct_cached_callable(func, contract)

            metadata = FunctionMetadata(
                name=func_name,
                func=final_func,
                contract=contract,
                registry=self,
                module=cached_data.get("module", ""),
                doc=cached_data.get("doc", ""),
                tags=cached_data.get("tags", []),
                original_name=cached_data.get("original_name", func_name),
                memory_type=cached_data.get("memory_type", self.get_memory_type()),
            )
            functions[func_name] = metadata

        return functions

    def get_discovery_signature(self) -> str:
        """Return the existing JSON cache's discovery-input signature."""
        signature = {
            "registry_class": f"{type(self).__module__}.{type(self).__qualname__}",
            "modules_to_scan": list(self.MODULES_TO_SCAN),
            "source_mtimes": self.cache_source_mtimes(),
            "context": self.cache_discovery_context(),
        }
        return json.dumps(signature, sort_keys=True)

    def cache_discovery_context(self) -> Mapping[str, Any]:
        """Return process facts that can change the discovered catalogue."""

        return {}

    def persistent_cache_path(self) -> Path:
        """Project the discovery context into its persistent cache identity."""

        context_source = json.dumps(
            self.cache_discovery_context(),
            sort_keys=True,
            separators=(",", ":"),
        )
        if context_source == "{}":
            return self._cache_path
        context_fingerprint = hashlib.sha256(context_source.encode()).hexdigest()
        return self._cache_path.with_name(
            f"{self._cache_path.stem}.{context_fingerprint}{self._cache_path.suffix}"
        )

    def cache_source_mtimes(self) -> Dict[str, float]:
        """Return implementation source mtimes that own discovery semantics."""

        source_paths = {
            Path(__file__),
            Path(inspect.getsourcefile(type(self)) or __file__),
        }
        return {
            str(source_path): source_path.stat().st_mtime
            for source_path in source_paths
            if source_path.exists()
        }

    def _save_to_cache(self, functions: Dict[str, FunctionMetadata]) -> None:
        """Save function metadata to cache."""
        cache_path = self.persistent_cache_path()
        writable_parent = self._writable_cache_parent()
        if writable_parent is None:
            logger.warning(
                "Registry cache path %s is not writable; using discovered "
                "%s functions without refreshing the disk cache.",
                cache_path,
                self.library_name,
            )
            return

        cache_data = {
            "cache_version": self.CACHE_FORMAT_VERSION,
            "library_version": self.get_library_version(),
            "discovery_signature": self.get_discovery_signature(),
            "timestamp": time.time(),
            "functions": {
                func_name: {
                    "name": metadata.name,
                    "original_name": metadata.original_name,
                    "module": metadata.module,
                    "memory_type": metadata.get_memory_type(),
                    "contract": metadata.contract.key,
                    "doc": metadata.doc,
                    "tags": metadata.tags,
                }
                for func_name, metadata in functions.items()
            },
        }

        atomic_write_json(cache_path, cache_data)

        logger.info(f"💾 Saved {len(functions)} {self.library_name} functions to cache")

    def _writable_cache_parent(self) -> Optional[str]:
        """Return the nearest existing writable cache parent, or None."""
        parent = self.persistent_cache_path().parent
        while not parent.exists():
            if parent.parent == parent:
                return None
            parent = parent.parent
        if not parent.is_dir():
            return None
        if not os.access(parent, os.W_OK | os.X_OK):
            return None
        return str(parent)

    def get_memory_type(self) -> str:
        """Get the memory type string value for this library."""
        return self.MEMORY_TYPE

    def get_module_patterns(self) -> List[str]:
        """Get module patterns that identify this library (can be overridden by implementations)."""
        # Default: just the library name
        return [self.library_name.lower()]

    def get_display_name(self) -> str:
        """Get display name for this library (can be overridden by implementations)."""
        # Default: capitalize library name
        return self.library_name.title()

    def public_projection_module(self, metadata: FunctionMetadata) -> str | None:
        """Declare the import module used for projected external callables."""

        return f"openhcs.{metadata.func.__module__}"

    # ===== FUNCTION DISCOVERY =====
    def get_modules_to_scan(self) -> List[Tuple[str, Any]]:
        """
        Get list of (module_name, module_object) tuples to scan for functions.
        Uses the MODULES_TO_SCAN class attribute and library object from get_library_object().

        Returns:
            List of (name, module) pairs where name is for identification
            and module is the actual module object to scan.
        """
        library = self.get_library_object()
        modules = []
        for module_name in self.MODULES_TO_SCAN:
            if module_name == "":
                # Empty string means scan the main library namespace
                module = library
                modules.append(("main", module))
            else:
                module = importlib.import_module(f"{library.__name__}.{module_name}")
                modules.append((module_name, module))
        return modules

    @abstractmethod
    def get_library_object(self):
        """Get the main library object to scan for modules. Library-specific implementation."""
        pass


class RuntimeTestingRegistryBase(LibraryRegistryBase):
    """
    Extended ABC for libraries that require runtime testing.

    Adds runtime testing methods for libraries that don't have explicit
    processing contracts and need behavioral classification through testing.
    """

    @staticmethod
    def probe_spatial_rank() -> int:
        """Spatial rank of the active axis family's payloads."""
        from openhcs.core.axes import AxisFamily

        return AxisFamily.active().payload_spatial_rank

    def create_test_arrays(self) -> Tuple[Any, Any]:
        """Return (stack probe, plane probe) at the active family's spatial rank."""
        plane_shape = (20,) * self.probe_spatial_rank()
        dtype = self._get_float_dtype()
        return (
            self._create_array((3, *plane_shape), dtype),
            self._create_array(plane_shape, dtype),
        )

    @abstractmethod
    def _create_array(self, shape: Tuple[int, ...], dtype):
        """Create array with specified shape and dtype. Library-specific implementation."""
        pass

    def _get_float_dtype(self):
        """Get the appropriate float dtype for this library."""
        return self.FLOAT_DTYPE

    # ===== CORE BEHAVIOR CONTRACT =====
    def classify_function_behavior(
        self,
        func: Callable,
    ) -> Tuple[type[ProcessingContract] | None, bool]:
        """Return the contract whose declaration explains the probe outcome."""
        test_3d, test_2d = self.create_test_arrays()

        def test_function(test_array):
            """Test one image call and retain only valid main-flow outputs."""
            try:
                result = func(test_array)
                if self._main_array_output(result) is None:
                    return False, None
                return True, result
            except Exception:
                return False, None

        works_3d, result_3d = test_function(test_3d)
        works_2d, _ = test_function(test_2d)
        main_output = None if result_3d is None else self._main_array_output(result_3d)
        contract = ProcessingContract.for_probe(
            ContractProbe(
                works_on_stack=works_3d,
                works_on_plane=works_2d,
                stack_result_rank=(
                    None if main_output is None else len(main_output.shape)
                ),
                spatial_rank=self.probe_spatial_rank(),
            )
        )
        return contract, works_3d or works_2d

    @staticmethod
    def _main_array_output(result: Any) -> Any | None:
        """Return the canonical image result accepted by processing contracts."""

        positional = runtime_output_tuple(result)
        if isinstance(positional, tuple):
            if not positional:
                return None
            positional = positional[0]
        if not is_array_payload(positional):
            return None
        return positional

    @abstractmethod
    def _stack_2d_results(self, func, test_3d):
        """Stack 2D results. Library-specific implementation required."""
        pass

    @abstractmethod
    def _arrays_close(self, arr1, arr2):
        """Compare arrays. Library-specific implementation required."""
        pass

    def runtime_owned_parameter_names(
        self,
        func: Callable[..., Any],
    ) -> tuple[str, ...]:
        """Keep non-authorable library controls at their declared defaults.

        Runtime-discovered libraries commonly expose callbacks, opaque values,
        and callable deprecation sentinels that cannot be authored faithfully by
        a parameter editor.  The shared runtime-tested declaration family owns
        that projection for every such library.
        """

        signature = inspect.signature(func)
        return tuple(
            parameter_name
            for parameter_name, parameter_info in SignatureAnalyzer.analyze(
                func,
                skip_first_param=False,
            ).items()
            if not self._annotation_has_authored_value(parameter_info.param_type)
            or self._has_callable_default(signature.parameters[parameter_name])
        )

    @classmethod
    def _annotation_has_authored_value(cls, annotation: object) -> bool:
        """Return whether an inferred annotation contains an editable value."""

        resolved = resolve_annotated(annotation)
        if is_union_type(resolved):
            return any(
                member is not type(None) and cls._annotation_has_authored_value(member)
                for member in get_args(resolved)
            )
        return resolved is not Any and get_origin(resolved) is not CallableABC

    @staticmethod
    def _has_callable_default(parameter: inspect.Parameter) -> bool:
        """Return whether a callable object is serving as a library default."""

        return parameter.default is not inspect.Parameter.empty and callable(
            parameter.default
        )

    def create_library_adapter(
        self, original_func: Callable, contract: type[ProcessingContract]
    ) -> Callable:
        """Create adapter with library-specific processing only."""
        import inspect

        func_name = original_func.__name__

        logger.debug(
            "CREATE LIBRARY ADAPTER: %s from %s",
            func_name,
            original_func.__module__,
        )

        # Get original signature to preserve it
        original_sig = inspect.signature(original_func)

        # Wrap external library functions with ArrayBridge decorator for dtype handling
        arraybridge_wrapped_func = original_func
        if self.MEMORY_TYPE is not None:
            from arraybridge import wrap_dtype_preserving_callable

            mem_type = MemoryType(self.MEMORY_TYPE)
            arraybridge_wrapped_func = wrap_dtype_preserving_callable(
                original_func,
                mem_type,
            )

        def adapter(image, *args, **kwargs):
            processed_image = self._preprocess_input(image, func_name)
            result = arraybridge_wrapped_func(processed_image, *args, **kwargs)
            return self._postprocess_output(result, image, func_name)

        # Apply wraps and preserve signature
        wrapped_adapter = wraps(original_func)(adapter)
        wrapped_adapter.__signature__ = original_sig

        # Preserve and enhance annotations
        wrapped_adapter.__annotations__ = inspect.get_annotations(
            original_func,
            eval_str=False,
        ).copy()

        # Extract type hints from docstring if annotations are missing
        self._enhance_annotations_from_docstring(wrapped_adapter, original_func)

        # Set memory type attributes for contract execution compatibility
        # Only set if registry has a specific memory type (external libraries)
        if self.MEMORY_TYPE is not None:
            for attribute in MemoryContractAttribute:
                attribute.write(wrapped_adapter, self.MEMORY_TYPE)

        _set_registry_runtime_parameter_exclusions(
            wrapped_adapter,
            original_sig,
            self.runtime_owned_parameter_names(wrapped_adapter),
            source=original_func,
        )

        return wrapped_adapter

    def _enhance_annotations_from_docstring(
        self, wrapped_func: Callable, original_func: Callable
    ) -> None:
        """Project generic signature analysis onto an unannotated library wrapper."""

        from python_introspect import SignatureAnalyzer

        inferred = SignatureAnalyzer.analyze(
            original_func,
            skip_first_param=False,
        )
        wrapped_func.__annotations__.update(
            {
                parameter_name: parameter_info.param_type
                for parameter_name, parameter_info in inferred.items()
                if parameter_name not in wrapped_func.__annotations__
                and parameter_info.param_type is not Any
            }
        )

    @abstractmethod
    def _preprocess_input(self, image, func_name: str):
        """Preprocess input image. Library-specific implementation."""
        pass

    @abstractmethod
    def _postprocess_output(self, result, original_image, func_name: str):
        """Postprocess output result. Library-specific implementation."""
        pass

    # ===== BASIC FILTERING =====
    def should_include_function(self, func: Callable, func_name: str) -> bool:
        """Single method for all filtering logic (blacklist, signature, etc.)"""
        # Skip private functions
        if func_name.startswith("_"):
            return False

        # Skip exclusions (check both common and library-specific)
        if func_name.lower() in self.EXCLUSIONS:
            return False

        # Skip classes and types
        if inspect.isclass(func) or isinstance(func, type):
            return False

        # Must be callable
        if not callable(func):
            return False

        # Pure functions must have at least one parameter
        sig = inspect.signature(func)
        params = list(sig.parameters.values())
        if not params:
            return False

        # Validate that type hints can be resolved (skip functions with missing dependencies)
        if not self._validate_type_hints(func, func_name):
            return False

        # Library-specific signature validation
        return self._check_first_parameter(params[0], func_name)

    def _validate_type_hints(self, func: Callable, func_name: str) -> bool:
        """
        Validate that function type hints can be resolved.

        Returns False if type hints reference missing dependencies (e.g., torch when not installed).
        This prevents functions with unresolvable type hints from being registered.
        """
        try:
            # Try to resolve type hints - this will fail if dependencies are missing
            get_type_hints(func)
            return True
        except NameError as e:
            # Type hint references a missing dependency (e.g., 'torch' not defined)
            logger.warning(
                f"Skipping function '{func_name}' due to unresolvable type hints: {e}"
            )
            return False
        except Exception:
            # Other type hint resolution errors - be conservative and allow the function
            # (this handles edge cases where get_type_hints fails for other reasons)
            return True

    @abstractmethod
    def _check_first_parameter(self, first_param, func_name: str) -> bool:
        """Check if first parameter meets library-specific criteria. Library-specific implementation."""
        pass

    # ===== RUNTIME TESTING IMPLEMENTATION =====
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover and classify all library functions with runtime testing."""
        functions = {}
        modules = self.get_modules_to_scan()
        logger.info(f"🔍 Starting function discovery for {self.library_name}")
        logger.info(
            f"📦 Scanning {len(modules)} modules: {[name for name, _ in modules]}"
        )

        total_tested = 0
        total_accepted = 0

        for module_name, module in modules:
            logger.info(f"  📦 Analyzing {module_name} ({module})...")
            module_tested = 0
            module_accepted = 0

            for name, func in inspect.getmembers(module):
                if name.startswith("_"):
                    continue
                full_path = self._get_full_function_path(module, name, module_name)

                if not self.should_include_function(func, name):
                    rejection_reason = self._get_rejection_reason(func, name)
                    if rejection_reason != "private":
                        logger.debug(f"    🚫 Skipping {full_path}: {rejection_reason}")
                    continue

                module_tested += 1
                total_tested += 1

                contract, is_valid = self.classify_function_behavior(func)
                logger.debug(f"    🧪 Testing {full_path}")
                logger.debug(
                    f"       Classification: {contract.key if contract else contract}"
                )

                if not is_valid:
                    logger.debug("       ❌ Rejected: Invalid classification")
                    continue

                doc = inspect.getdoc(func)
                doc_lines = doc.splitlines() if doc is not None else ()
                first_line_doc = doc_lines[0] if doc_lines else ""
                module_path = func.__module__
                if module_path is None:
                    module_path = ""
                func_name = self._generate_function_name(name, module_name)

                # Apply library adapter (preprocessing/postprocessing)
                adapted_func = self.create_library_adapter(func, contract)

                # Apply nominal contract wrapper.
                final_func = self.apply_contract_wrapper(adapted_func, contract)

                metadata = FunctionMetadata(
                    name=func_name,
                    func=final_func,
                    contract=contract,
                    registry=self,
                    module=module_path,
                    doc=first_line_doc,
                    tags=self._generate_tags(name),
                    original_name=name,
                    memory_type=self.get_memory_type(),
                )

                functions[func_name] = metadata
                module_accepted += 1
                total_accepted += 1
                logger.debug(f"       ✅ Accepted as '{func_name}'")

            logger.debug(
                f"  📊 Module {module_name}: {module_accepted}/{module_tested} functions accepted"
            )

        logger.info(
            f"✅ Discovery complete: {total_accepted}/{total_tested} functions accepted"
        )
        return functions

    def _get_full_function_path(self, module, func_name: str, module_name: str) -> str:
        """Generate full module path for logging."""
        if module_name == "main":
            return f"{self.library_name}.{func_name}"
        else:
            # Extract clean module path
            module_str = str(module)
            if "'" in module_str:
                clean_path = module_str.split("'")[1]
                return f"{clean_path}.{func_name}"
            else:
                return f"{module_name}.{func_name}"

    def _get_rejection_reason(self, func: Callable, func_name: str) -> str:
        """Get detailed reason why a function was rejected."""
        # Check each rejection criteria in order
        if func_name.startswith("_"):
            return "private"

        if func_name.lower() in self.EXCLUSIONS:
            return "blacklisted"

        if inspect.isclass(func) or isinstance(func, type):
            return "is class/type"

        if not callable(func):
            return "not callable"

        sig = inspect.signature(func)
        params = list(sig.parameters.values())
        if not params:
            return "no parameters (not pure function)"

        return "unknown"

    # ===== CUSTOMIZATION HOOKS =====
    def _generate_function_name(self, name: str, module_name: str) -> str:
        """Generate function name. Override in subclasses for custom naming."""
        return name

    def _generate_tags(self, func_name: str) -> List[str]:
        """Generate tags using library name."""
        return [self.library_name]


# ============================================================================
# Registry Export
# ============================================================================
# Auto-created registry from LibraryRegistryBase
LIBRARY_REGISTRIES = LibraryRegistryBase.__registry__
