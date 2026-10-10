"""
Consolidated orchestrator module for OpenHCS.

This module provides a unified PipelineOrchestrator class that implements
a two-phase (compile-all-then-execute-all) pipeline execution model.
"""

import logging
from pathlib import Path
from typing import TYPE_CHECKING, Any, Callable, Dict, List, Optional, Union

from openhcs.constants.constants import Backend, OrchestratorState
from openhcs.core.compiled_execution import CompiledExecutionBundle
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.execution_visualizer import ExecutionVisualizerABC
from objectstate.object_state import ObjectState
from objectstate.object_state_registry import ObjectStateRegistry
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG, OpenHCSZMQConfig


from openhcs.core.metadata_cache import MetadataCache
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.input_workspace import InputWorkspacePreparationResult
from openhcs.core.source_binding_context import SourceBindingContext
from openhcs.core.source_bindings import source_bindings_defaults_to_base
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.steps.abstract import AbstractStep

from openhcs.core.orchestrator.execution_result import (
    ExecutionResult,
    RuntimeObservationMode,
)
from openhcs.core.orchestrator.cancellation import ExecutionCancellationAuthority
from openhcs.core.orchestrator.compiled_plate_execution import (
    CompiledPlateExecutionRequest,
    execute_compiled_plate_request,
)
from openhcs.core.debug import (
    DebugExecutionPolicy,
    NoOpDebugExecutionPolicy,
)
from openhcs.core.progress import ProgressExecutionContext
from openhcs.core.viewer_streaming_service import StreamingViewerLifecycle
from openhcs.runtime.viewer_protocol import ViewerPersistenceMode
from polystore.filemanager import FileManager

if TYPE_CHECKING:
    from openhcs.core.orchestrator.worker_execution import PreparedForkWorkerLaneRunner
    from openhcs.core.config import PipelineConfig

# Zarr backend is CPU-only; always import it (even in subprocess/no-GPU mode)
from polystore.zarr import ZarrStorageBackend

# PipelineConfig now imported directly above
from openhcs.core.dataset_sources.source import DatasetSource
from openhcs.core.post_execute import PostExecuteHook
from openhcs.core.alias_property import AliasProperty
from openhcs.core.axes import Axis, AxisFamily, GroupingDeclaration

# Import generic component system - required for orchestrator functionality

logger = logging.getLogger(__name__)


class PipelineOrchestrator:
    """
    Updated orchestrator supporting both global and per-orchestrator configuration.

    Global configuration: Updates all orchestrators (existing behavior)
    Per-orchestrator configuration: Affects only this orchestrator instance

    The orchestrator first compiles the pipeline for all specified axis values,
    creating frozen, immutable ProcessingContexts using `compile_plate_for_processing()`.
    Then, it executes the (now stateless) pipeline definition against these contexts,
    potentially in parallel, using `execute_compiled_plate()`.
    """

    # ObjectState delegation: when ObjectState stores this orchestrator, extract
    # editable parameters from pipeline_config (a dataclass) instead of the orchestrator.
    # This enables time-travel to track the orchestrator lifecycle while forms edit the config.
    __objectstate_delegate__ = "pipeline_config"
    _plate_path: Optional[Path] = None
    _plate_path_frozen: bool = False
    state: AliasProperty[OrchestratorState] = AliasProperty("_state")

    def __init__(
        self,
        plate_path: Union[str, Path],
        workspace_path: Optional[Union[str, Path]] = None,
        *,
        pipeline_config: Optional["PipelineConfig"] = None,
        resolved_config: GlobalPipelineConfig | None = None,
        storage_registry: Optional[Any] = None,
        selected_pipeline_path: Union[str, Path, None] = None,
        progress_callback: Optional[Callable[[Dict[str, Any]], None]] = None,
        transport_config: OpenHCSZMQConfig = OPENHCS_ZMQ_CONFIG,
    ):
        self._initialize_runtime_identity(
            plate_path,
            workspace_path,
            pipeline_config=pipeline_config,
            selected_pipeline_path=selected_pipeline_path,
            transport_config=transport_config,
        )
        if storage_registry:
            self.registry = storage_registry
            logger.info("PipelineOrchestrator using provided StorageRegistry instance.")
        else:
            # FileManager snapshots the mapping while preserving physical backend
            # identities, including the memory backend cleared between executions.
            from polystore.base import (
                storage_registry as global_storage_registry,
                ensure_storage_registry,
            )

            # Ensure registry is initialized
            ensure_storage_registry()
            self.registry = global_storage_registry
            logger.info("PipelineOrchestrator using global StorageRegistry instance.")

        # Override zarr backend with orchestrator's resolved config.
        effective_config = (
            self.get_effective_config() if resolved_config is None else resolved_config
        )
        zarr_backend_with_config = ZarrStorageBackend(effective_config.zarr_config)
        self.registry[Backend.ZARR.value] = zarr_backend_with_config
        logger.info(
            f"Orchestrator zarr backend configured with {effective_config.zarr_config.compressor.value} compression"
        )

        self.filemanager = FileManager(self.registry)
        self._initialize_runtime_services(progress_callback)

    @classmethod
    def from_compiled_execution(
        cls,
        execution_bundle: CompiledExecutionBundle,
        *,
        plate_path: Union[str, Path],
        pipeline_config: "PipelineConfig",
        selected_pipeline_path: Union[str, Path, None] = None,
        progress_callback: Optional[Callable[[Dict[str, Any]], None]] = None,
        transport_config: OpenHCSZMQConfig = OPENHCS_ZMQ_CONFIG,
    ) -> "PipelineOrchestrator":
        """Create fresh runtime services around an admitted compiled domain."""
        contexts = tuple(execution_bundle.runtime_contexts.values())
        if not contexts:
            raise ValueError("Compile artifact missing compiled_contexts")
        source = contexts[0]
        if source.filemanager is None:
            raise ValueError("Compiled execution lacks its admitted source workspace.")
        orchestrator = cls.__new__(cls)
        orchestrator._initialize_runtime_identity(
            plate_path,
            source.workspace_path,
            pipeline_config=pipeline_config,
            selected_pipeline_path=selected_pipeline_path,
            transport_config=transport_config,
        )
        orchestrator.registry = source.filemanager.registry
        orchestrator._initialize_runtime_services(progress_callback)
        return orchestrator.adopt_compiled_execution(execution_bundle)

    def _initialize_runtime_identity(
        self,
        plate_path: Union[str, Path],
        workspace_path: Optional[Union[str, Path]],
        *,
        pipeline_config: Optional["PipelineConfig"],
        selected_pipeline_path: Union[str, Path, None],
        transport_config: OpenHCSZMQConfig,
    ) -> None:
        self._executor_resources = None
        self._execution_cancellation = ExecutionCancellationAuthority()
        self.execution_id = f"local::{plate_path}"
        self.transport_config = transport_config
        self._pipeline_config = None

        from openhcs.core.config import PipelineConfig

        self.pipeline_config = (
            PipelineConfig() if pipeline_config is None else pipeline_config
        )

        # Convert to the immutable execution identity. Source availability is a
        # runtime initialization precondition so declarations can be loaded and
        # edited while their external source is temporarily unavailable.
        if plate_path:
            plate_path = Path(plate_path)
            if not plate_path.is_absolute():
                raise ValueError(f"Plate path must be absolute: {plate_path}")

        self._plate_path_frozen = False

        self.plate_path = plate_path
        self.workspace_path = workspace_path
        self.source_plate_path = plate_path
        self.input_workspace_preparation_result: (
            InputWorkspacePreparationResult | None
        ) = None
        self.selected_pipeline_path = (
            Path(selected_pipeline_path) if selected_pipeline_path is not None else None
        )

        if self.plate_path is None and self.workspace_path is None:
            raise ValueError(
                "Either plate_path or workspace_path must be provided for PipelineOrchestrator."
            )

        # Freeze plate_path immediately after setting it to prove immutability
        self._plate_path_frozen = True
        logger.info(f"🔒 PLATE_PATH FROZEN: {self.plate_path} is now immutable")

    def _initialize_runtime_services(
        self, progress_callback: Optional[Callable[[Dict[str, Any]], None]]
    ) -> None:
        self.input_dir: Optional[Path] = None
        self.microscope_handler: Optional[DatasetSource] = None
        self._microscope_handler_rebuild_type: type[DatasetSource] | None = None
        self.default_pipeline_definition: Optional[List[AbstractStep]] = None
        self._initialized: bool = False
        self._state: OrchestratorState = OrchestratorState.CREATED

        # Progress callback for real-time execution updates
        self.progress_callback = progress_callback
        if progress_callback:
            logger.info("PipelineOrchestrator initialized with progress callback")

        # Component keys cache for every declared axis (including the partition axis)
        self._component_keys_cache: Dict[type[Axis], List[str]] = {}

        self.metadata_cache = MetadataCache()

        # Viewer management - shared between pipeline execution and image browser
        self._visualizers = {}  # Dict[(backend_name, port)] -> visualizer instance

    @property
    def plate_path(self) -> Optional[Path]:
        """Execution plate path for this orchestrator."""

        return self._plate_path

    @plate_path.setter
    def plate_path(self, value: Optional[Path]) -> None:
        """Set plate path until the orchestrator freezes execution identity."""

        if self._plate_path_frozen:
            import traceback

            stack_trace = "".join(traceback.format_stack())
            error_msg = (
                f"🚫 IMMUTABLE PLATE_PATH VIOLATION: Cannot modify plate_path after freezing!\n"
                f"Current value: {self._plate_path}\n"
                f"Attempted new value: {value}\n"
                f"Stack trace:\n{stack_trace}"
            )
            logger.error(error_msg)
            raise AttributeError(error_msg)
        self._plate_path = value

    def get_or_create_visualizer(self, config, vis_config=None):
        """
        Get existing visualizer or create a new one for the given config.

        This method is shared between pipeline execution and image browser to avoid
        duplicating viewer instances. Viewers are tracked by (backend_name, port) key.

        Args:
            config: Streaming config (any StreamingConfig subclass)
            vis_config: Optional visualizer config (can be None for image browser)

        Returns:
            Visualizer instance
        """
        from openhcs.core.config import StreamingConfig

        # Streaming configs should be managed by the centralized ViewerStateManager
        if isinstance(config, StreamingConfig):
            key = (config.viewer_type, config.port)
            persistence_mode = ViewerPersistenceMode.from_flag(config.persistent)

            viewer = StreamingViewerLifecycle.get_or_create_visualizer(
                filemanager=self.filemanager,
                config=config,
                visualizer_config=vis_config,
                transport_config=self.transport_config,
                fresh=persistence_mode.execution_session_owns_process,
                ready_timeout=30.0,
            )

            # Keep a reference for backward compatibility
            self._visualizers[key] = viewer
            return viewer

        # Non-streaming (local) visualizers: create and start synchronously
        vis = config.create_visualizer(
            self.filemanager,
            vis_config,
            self.transport_config,
        )
        vis.start_viewer()

        # Store for compatibility
        backend_name = config.backend.name
        self._visualizers[(backend_name,)] = vis
        return vis

    def initialize_microscope_handler(
        self, resolved_config: GlobalPipelineConfig | None = None
    ):
        """Initializes the microscope handler."""
        if self.microscope_handler is not None:
            logger.debug("Microscope handler already initialized.")
            return
        #        if self.input_dir is None:
        #            raise RuntimeError("Workspace (and input_dir) must be initialized before microscope handler.")

        logger.info(
            f"Initializing microscope handler using input directory: {self.input_dir}..."
        )
        try:
            shared_context = (
                self.get_effective_config()
                if resolved_config is None
                else resolved_config
            )
            if self._microscope_handler_rebuild_type is None:
                self.microscope_handler = shared_context.dataset_source.open(
                    self.plate_path,
                    filemanager=self.filemanager,
                    source_bindings_config=shared_context.source_bindings_config,
                )
            else:
                self.microscope_handler = self._microscope_handler_rebuild_type.create(
                    filemanager=self.filemanager,
                    source_bindings_config=shared_context.source_bindings_config,
                )
                self.microscope_handler.plate_folder = Path(self.plate_path)
                self._microscope_handler_rebuild_type = None
            logger.info(
                f"Initialized microscope handler: {type(self.microscope_handler).__name__}"
            )
        except Exception as e:
            error_msg = f"Failed to create microscope handler: {e}"
            logger.error(error_msg)
            raise RuntimeError(error_msg) from e

    def bind_input_workspace(
        self,
        result: InputWorkspacePreparationResult,
    ) -> None:
        """Bind a caller-prepared generic input workspace before initialization."""

        if self._initialized or self.state is not OrchestratorState.CREATED:
            raise RuntimeError(
                "An input workspace can only be bound before initialization."
            )
        self.input_workspace_preparation_result = result
        self.source_plate_path = Path(result.original_source_root)
        if Path(result.execution_plate_path) == Path(self.plate_path):
            return
        self._rebind_plate_path_for_prepared_workspace(result.execution_plate_path)

    def source_binding_context(self, logical_plate_id: str) -> SourceBindingContext:
        """Project the current source declaration and workspace owned by this plate."""

        if not logical_plate_id:
            raise ValueError("Source-binding context requires a logical plate id.")
        if self.source_plate_path is None or self.plate_path is None:
            raise RuntimeError("Source-binding context requires a bound plate path.")
        if self.pipeline_config is None:
            raise RuntimeError("Source-binding context requires a PipelineConfig.")
        return SourceBindingContext(
            logical_plate_id=logical_plate_id,
            display_plate_root=self.source_plate_path,
            execution_plate_path=self.plate_path,
            source_bindings=source_bindings_defaults_to_base(
                self.pipeline_config.source_bindings_config
            ),
            filemanager=self.filemanager,
            source_backend=Backend.DISK.value,
        )

    def _rebind_plate_path_for_prepared_workspace(
        self,
        execution_plate_path: Path,
    ) -> None:
        """Bind CREATED orchestrator execution to its prepared input workspace."""

        if self._initialized or self.state is not OrchestratorState.CREATED:
            raise RuntimeError(
                "Prepared input workspace can only rebind a CREATED orchestrator."
            )
        self._rebind_created_plate_path(Path(execution_plate_path))
        self.execution_id = f"local::{self.plate_path}"
        logger.info(
            "Prepared input workspace rebound orchestrator execution path to %s",
            self.plate_path,
        )

    def _rebind_created_plate_path(self, execution_plate_path: Path) -> None:
        self._plate_path_frozen = False
        try:
            self.plate_path = execution_plate_path
        finally:
            self._plate_path_frozen = True

    def initialize(
        self,
        workspace_path: Optional[Union[str, Path]] = None,
        *,
        resolved_config: GlobalPipelineConfig | None = None,
    ) -> "PipelineOrchestrator":
        """
        Initializes all required components for the orchestrator.
        Must be called before other processing methods.
        Returns self for chaining.
        """
        if self._initialized:
            logger.info("Orchestrator already initialized.")
            return self

        try:
            effective_config = (
                self.get_effective_config()
                if resolved_config is None
                else resolved_config
            )
            self.initialize_microscope_handler(effective_config)
            self.microscope_handler.source_selection_role().require_available_source(
                self.plate_path
            )

            # Delegate workspace initialization to microscope handler
            logger.info("Initializing workspace with microscope handler...")
            actual_image_dir = self.microscope_handler.initialize_workspace(
                self.plate_path, self.filemanager
            )

            # Use the actual image directory returned by the microscope handler
            # All handlers now return Path (including OMERO with virtual paths)
            self.input_dir = Path(actual_image_dir)
            logger.info(f"Set input directory to: {self.input_dir}")

            # Log effective backend intent early for debugging test/UI differences
            try:
                vfs_cfg = effective_config.vfs_config
                logger.info(
                    "VFS config at init: read_backend=%s intermediate_backend=%s materialization_backend=%s",
                    vfs_cfg.read_backend,
                    vfs_cfg.intermediate_backend,
                    vfs_cfg.materialization_backend,
                )
            except Exception:
                logger.debug("Could not log VFS config at init", exc_info=True)

            # Set workspace_path based on what the handler returned
            if actual_image_dir != self.plate_path:
                # Handler created a workspace (or virtual path for OMERO)
                self.workspace_path = (
                    Path(actual_image_dir).parent
                    if Path(actual_image_dir).name != "workspace"
                    else Path(actual_image_dir)
                )
            else:
                # Handler used plate directly (like OpenHCS)
                self.workspace_path = None

            # Mark as initialized BEFORE caching to avoid chicken-and-egg problem
            self._initialized = True
            self._state = OrchestratorState.READY

            # Auto-cache component keys and metadata for instant access
            logger.info("Caching component keys and metadata...")
            self.cache_component_keys()
            self.metadata_cache.cache_metadata(
                self.microscope_handler, self.plate_path, self._component_keys_cache
            )

            # Ensure complete OpenHCS metadata exists
            self._ensure_openhcs_metadata(effective_config)

            logger.info(
                "PipelineOrchestrator fully initialized with cached component keys and metadata."
            )
            return self
        except Exception as e:
            self._state = OrchestratorState.INIT_FAILED
            logger.error(f"Failed to initialize orchestrator: {e}")
            raise

    def adopt_compiled_execution(
        self,
        execution_bundle: CompiledExecutionBundle,
    ) -> "PipelineOrchestrator":
        """Bind an admitted compiled source domain to this fresh runtime owner."""
        if self._initialized or self.state is not OrchestratorState.CREATED:
            raise RuntimeError(
                "Compiled execution can only be adopted before initialization."
            )
        contexts = tuple(execution_bundle.runtime_contexts.values())
        if not contexts:
            raise ValueError("Compile artifact missing compiled_contexts")
        source = contexts[0]
        if (
            source.microscope_handler is None
            or source.input_dir is None
            or source.filemanager is None
        ):
            raise ValueError("Compiled execution lacks its admitted source workspace.")
        source_registry = source.filemanager.registry
        for context in contexts:
            if (
                context.plate_path != self.plate_path
                or context.input_dir != source.input_dir
                or context.workspace_path != source.workspace_path
                or context.microscope_handler is not source.microscope_handler
                or context.filemanager is None
                or context.filemanager.registry.keys() != source_registry.keys()
                or any(
                    backend is not source_registry[name]
                    for name, backend in context.filemanager.registry.items()
                )
            ):
                raise ValueError(
                    "Compiled execution source domain does not match this runtime."
                )
        if source_registry.get(Backend.MEMORY.value) is not self.registry.get(
            Backend.MEMORY.value
        ):
            raise ValueError(
                "Compiled execution memory backend does not match this runtime."
            )
        source.microscope_handler.source_selection_role().require_available_source(
            self.plate_path
        )
        self.registry = dict(source_registry)
        self.filemanager = FileManager(self.registry)
        self.microscope_handler = source.microscope_handler
        self.input_dir = source.input_dir
        self.workspace_path = source.workspace_path
        self.default_pipeline_definition = list(execution_bundle.pipeline_definition)

        self._component_keys_cache[AxisFamily.active().partition_axis()] = list(
            execution_bundle.axis_ids
        )
        self._initialized = True
        self._state = OrchestratorState.READY
        return self

    def is_initialized(self) -> bool:
        return self._initialized

    def _ensure_openhcs_metadata(self, resolved_config: GlobalPipelineConfig) -> None:
        """Ensure complete OpenHCS metadata exists for the plate.

        Uses the same context creation logic as pipeline execution to get full metadata
        with channel names from metadata files (HTD, Index.xml, etc).

        Skips remote-service handlers because they do not have local source
        directories.
        """
        from openhcs.core.dataset_sources.openhcs_format import (
            OpenHCSMetadataGenerator,
            get_subdirectory_name,
        )

        source_role = self.microscope_handler.source_selection_role()
        if not source_role.requires_local_directory:
            logger.debug("Skipping local metadata creation for %s", source_role.role_name)
            return

        # For plates with virtual workspace, metadata is already created by _build_virtual_mapping()
        # We just need to add the component metadata to the existing "." subdirectory
        subdir_name = get_subdirectory_name(self.input_dir, self.plate_path)

        # Create context using SAME logic as create_context() to get full metadata
        context = self.create_context(
            axis_id="metadata_init", resolved_config=resolved_config
        )

        # Determine correct backend using handler's logic (virtual_workspace for ImageXpress/Opera, disk for others)
        backend = self.microscope_handler.get_primary_backend(
            self.plate_path, self.filemanager
        )
        logger.debug(f"Using backend '{backend}' for metadata extraction")

        # Create metadata (will skip if already complete)
        generator = OpenHCSMetadataGenerator(self.filemanager)
        generator.create_metadata(
            context,
            str(self.input_dir),
            backend,
            is_main=True,
            plate_root=str(self.plate_path),
            sub_dir=subdir_name,
            skip_if_complete=True,
        )

    def get_results_path(self) -> Path:
        """Get the results directory path for this orchestrator's plate.

        Uses the same logic as PathPlanner._get_results_path() to ensure consistency.
        This is the single source of truth for where results are stored.

        Returns:
            Path to results directory (absolute or relative to output plate root)
        """
        from openhcs.core.pipeline.path_planner import PipelinePathPlanner

        effective_config = self.get_effective_config()
        materialization_path = effective_config.materialization_results_path

        # If absolute, use as-is
        if Path(materialization_path).is_absolute():
            return Path(materialization_path)

        # If relative, resolve relative to output plate root
        path_config = effective_config.path_planning_config
        output_plate_root = PipelinePathPlanner.build_output_plate_root(
            self.plate_path, path_config, is_per_step_materialization=False
        )

        return output_plate_root / materialization_path

    def create_context(
        self, axis_id: str, *, resolved_config: GlobalPipelineConfig | None = None
    ) -> ProcessingContext:
        """Creates a ProcessingContext for a given multiprocessing axis value."""
        if not self.is_initialized():
            raise RuntimeError(
                "Orchestrator must be initialized before calling create_context()."
            )
        if not axis_id:
            raise ValueError("Axis identifier must be provided.")
        if self.input_dir is None:
            raise RuntimeError(
                "Orchestrator input_dir is not set; initialize orchestrator first."
            )

        effective_config = (
            self.get_effective_config() if resolved_config is None else resolved_config
        )
        context = ProcessingContext(
            axis_id=axis_id,
            filemanager=self.filemanager,
            tiff_config=effective_config.tiff_config,
            post_execute_hooks=PostExecuteHook.bind_all(effective_config),
            transport_config=self.transport_config,
        )
        # Orchestrator reference removed - was orphaned and unpickleable
        context.microscope_handler = self.microscope_handler
        context.input_dir = self.input_dir
        context.workspace_path = self.workspace_path
        context.plate_path = self.plate_path  # Add plate_path for path planner

        # CRITICAL: Pass metadata cache for OpenHCS metadata creation
        # Extract cached metadata from service and convert to dict format expected by OpenHCSMetadataGenerator
        metadata_dict = {}
        for component in AxisFamily.active().axes:
            cached_metadata = self.metadata_cache.get_cached_metadata(
                component
            )
            if cached_metadata:
                metadata_dict[component] = cached_metadata
        context.metadata_cache = metadata_dict

        return context

    def source_workspace_projection(
        self, *, resolved_config: GlobalPipelineConfig | None = None
    ):
        """Return the canonical resolved source state for the initialized plate.

        The projection carries every named alias, sample/well, site, channel, Z,
        timepoint, and backend-owned pixel reference used by compilation, runtime,
        and UI inspection. Consumers must query this view rather than constructing
        a second metadata model.

        Compilation supplies its already-resolved configuration; live inspection
        resolves the current saved configuration at this query boundary.
        """
        if not self.is_initialized():
            raise RuntimeError(
                "Orchestrator must be initialized before source workspace inspection."
            )
        if self.plate_path is None or self.microscope_handler is None:
            raise RuntimeError("Orchestrator source workspace is not available.")

        plate_path = Path(self.plate_path)
        from openhcs.core.source_workspace_projection import (
            VirtualWorkspaceSourceProjection,
            WorkspaceSourceProjections,
        )

        projection = WorkspaceSourceProjections.from_plate_metadata(
            plate_path=plate_path,
            metadata_handler=self.microscope_handler.metadata_handler,
            filemanager=self.filemanager,
            source_bindings=source_bindings_defaults_to_base(
                (
                    self.get_effective_config()
                    if resolved_config is None
                    else resolved_config
                ).source_bindings_config
            ),
        ).projection_if_available()
        if projection is not None:
            return projection
        return VirtualWorkspaceSourceProjection.empty(plate_path)

    def source_workspace_files(self, axis_id: str | None = None) -> tuple[str, ...]:
        """Return VFS-visible virtual source paths for one axis or all axes."""
        return self.source_workspace_projection().pipeline_start_files(axis_id=axis_id)

    def compile_pipelines(
        self,
        pipeline_definition: List[AbstractStep],
        well_filter: Optional[List[str]] = None,
        enable_visualizer_override: bool = False,
        is_zmq_execution: bool = False,
        debug_execution_policy: DebugExecutionPolicy = NoOpDebugExecutionPolicy(),
        *,
        resolved_config: GlobalPipelineConfig | None = None,
    ) -> CompiledExecutionBundle:
        """Compile the selected axes into one typed execution bundle."""
        return PipelineCompiler.compile_pipelines(
            orchestrator=self,
            pipeline_definition=pipeline_definition,
            axis_filter=well_filter,  # Translate well_filter to axis_filter for generic backend
            enable_visualizer_override=enable_visualizer_override,
            is_zmq_execution=is_zmq_execution,
            debug_execution_policy=debug_execution_policy,
            resolved_config=resolved_config,
        )

    def cancel_execution(self) -> int:
        """
        Cancel ongoing execution by shutting down the executor.

        This gracefully cancels pending futures and shuts down worker processes
        without killing all child processes (preserving Napari viewers, etc.).
        """
        self._execution_cancellation.request()

        if self._executor_resources is not None:
            return self._executor_resources.cancel_execution()
        return 0

    def execute_compiled_plate(
        self,
        execution_bundle: CompiledExecutionBundle,
        max_workers: Optional[int] = None,
        visualizer: ExecutionVisualizerABC | None = None,
        log_file_base: Optional[str] = None,
        progress_queue=None,
        progress_context=None,
        runtime_observation_mode: RuntimeObservationMode | None = None,
        debug_execution_policy: DebugExecutionPolicy = NoOpDebugExecutionPolicy(),
        prepared_worker_runner: "PreparedForkWorkerLaneRunner | None" = None,
    ) -> Dict[str, ExecutionResult]:
        """
        Execute-all phase: Runs the stateless pipeline against compiled contexts.

        Args:
            pipeline_definition: The stateless list of AbstractStep objects.
            compiled_contexts: Dict of axis_id to its compiled, frozen ProcessingContext.
                               Obtained from `compile_plate_for_processing`.
            max_workers: Maximum number of worker threads for parallel execution.
            visualizer: Viewer implementing the compiled execution lifecycle.
            log_file_base: Base path for worker process log files (without extension).
                          Each worker will create its own log file: {log_file_base}_worker_{pid}.log

        Returns:
            A dictionary mapping well IDs to their execution status (success/error and details).
        """
        if progress_context is None:
            raise ValueError("progress_context is required for execute_compiled_plate.")
        execution_progress_context = ProgressExecutionContext.from_value(
            progress_context
        )

        return execute_compiled_plate_request(
            self,
            CompiledPlateExecutionRequest(
                execution_id=execution_progress_context.execution_id,
                plate_id=execution_progress_context.plate_id,
                execution_bundle=execution_bundle,
                max_workers=max_workers,
                visualizer=visualizer,
                log_file_base=log_file_base,
                progress_queue=progress_queue,
                runtime_observation_mode=(
                    RuntimeObservationMode.for_compiled_bundle(execution_bundle)
                    if runtime_observation_mode is None
                    else runtime_observation_mode
                ),
                debug_execution_policy=debug_execution_policy,
                prepared_worker_runner=prepared_worker_runner,
            ),
        )

    def get_component_keys(
        self,
        component: type[GroupingDeclaration],
        component_filter: Optional[List[Union[str, int]]] = None,
        *,
        resolved_config: GlobalPipelineConfig | None = None,
    ) -> List[str]:
        """
        Return the discovered values of one declared axis.

        Returns the discovered component values as strings to match the pattern
        detection system format.

        Tries metadata cache first, falls back to filename parsing cache if metadata is empty.

        Args:
            component: The axis whose values to return; a step's grouping
                      declaration is accepted when it names one axis
            component_filter: Optional list of component values to filter by
            resolved_config: Existing compilation configuration. Omit for live
                inspection of the current saved declaration.

        Returns:
            List of component values as strings, sorted

        Raises:
            RuntimeError: If orchestrator is not initialized
        """
        if not self.is_initialized():
            raise RuntimeError(
                "Orchestrator must be initialized before getting component keys."
            )

        grouping_axes = component.grouping_axes()
        if len(grouping_axes) != 1:
            raise ValueError(f"Cannot get component keys for {component!r}")
        (component,) = grouping_axes

        effective_config = (
            self.get_effective_config() if resolved_config is None else resolved_config
        )
        source_bindings = source_bindings_defaults_to_base(
            effective_config.source_bindings_config
        )
        # Use component directly - let natural errors occur for wrong types
        component_name = component.name

        # Try metadata cache first (preferred source)
        cached_metadata = self.metadata_cache.get_cached_metadata(component)
        if source_bindings.source_filter_declarations:
            all_components = list(
                self.source_workspace_projection(
                    resolved_config=effective_config
                ).component_values(component)
            )
        elif cached_metadata:
            all_components = list(cached_metadata.keys())
            logger.debug(
                f"Using metadata cache for {component_name}: {len(all_components)} components"
            )
        else:
            # Fall back to filename parsing cache
            all_components = self._component_keys_cache[
                component
            ]  # Let KeyError bubble up naturally

            if not all_components:
                logger.warning(
                    f"No {component_name} values found in input directory: {self.input_dir}"
                )
                return []

            logger.debug(
                f"Using filename parsing cache for {component.name}: {len(all_components)} components"
            )

        if component_filter:
            str_component_filter = {str(c) for c in component_filter}
            selected_components = [
                comp for comp in all_components if comp in str_component_filter
            ]
            if not selected_components:
                logger.warning(
                    f"No {component_name} values from {all_components} match the filter: {component_filter}"
                )
            return selected_components
        else:
            return all_components

    def cache_component_keys(
        self, components: Optional[List[type[Axis]]] = None
    ) -> None:
        """
        Pre-compute and cache component keys for fast access using single-pass parsing.

        This method performs expensive file listing and parsing operations once,
        extracting all component types in a single pass for maximum efficiency.

        Args:
            components: Optional list of axes to cache.
                       If None, caches every axis of the active family.
        """
        if not self.is_initialized():
            raise RuntimeError(
                "Orchestrator must be initialized before caching component keys."
            )

        if components is None:
            components = list(AxisFamily.active().axes)

        logger.info(
            f"Caching component keys for: {[comp.name for comp in components]}"
        )

        try:
            axis_values = self.microscope_handler.axis_values(
                self.input_dir, self.filemanager, components
            )
        except Exception as e:
            logger.error(
                f"Error listing files or parsing filenames from {self.input_dir}: {e}",
                exc_info=True,
            )
            axis_values = {component: [] for component in components}

        for component, values in axis_values.items():
            self._component_keys_cache[component] = values
            if not values:
                logger.warning(
                    f"No {component.name} values found in input directory: {self.input_dir}"
                )

        logger.info(
            f"Component key caching complete. Cached {len(axis_values)} axes in single pass."
        )

    def clear_component_cache(
        self, components: Optional[List[type[Axis]]] = None
    ) -> None:
        """
        Clear cached component keys to force recomputation.

        Use this when the input directory contents have changed and you need
        to refresh the component key cache.

        Args:
            components: Optional list of axes to clear from cache.
                       If None, clears entire cache.
        """
        if components is None:
            self._component_keys_cache.clear()
            logger.info("Cleared entire component keys cache")
        else:
            for component in components:
                if component in self._component_keys_cache:
                    del self._component_keys_cache[component]
                    logger.debug(f"Cleared cache for {component.name}")

            logger.info(f"Cleared cache for {len(components)} component types")

    # Global config management removed - handled by UI layer

    @property
    def pipeline_config(self) -> Optional["PipelineConfig"]:
        """Get current pipeline configuration."""
        return self._pipeline_config

    @pipeline_config.setter
    def pipeline_config(self, value: Optional["PipelineConfig"]) -> None:
        """Replace the declaration through source invalidation once bound to a plate."""
        if value is None or self.plate_path is None:
            self._pipeline_config = value
        else:
            self.apply_pipeline_config(value)

    def apply_pipeline_config(self, pipeline_config: "PipelineConfig") -> None:
        """
        Replace the declaration and invalidate changed source bindings.

        Saved inheritance is resolved without modifying global thread-local state.
        """
        # Import PipelineConfig at runtime for isinstance check
        from openhcs.core.config import PipelineConfig

        if not isinstance(pipeline_config, PipelineConfig):
            raise TypeError(f"Expected PipelineConfig, got {type(pipeline_config)}")

        previous_config = self._pipeline_config
        previous_source_bindings = None
        if previous_config is not None:
            previous_resolved, _ = ObjectState.resolve_saved_object(
                previous_config,
                ancestor_objects_with_scopes=(
                    ObjectStateRegistry.get_ancestor_objects_with_scopes(
                        None, use_saved=True
                    )
                ),
            )
            previous_source_bindings = previous_resolved.source_bindings_config
        current_resolved, _ = ObjectState.resolve_saved_object(
            pipeline_config,
            ancestor_objects_with_scopes=(
                ObjectStateRegistry.get_ancestor_objects_with_scopes(
                    None, use_saved=True
                )
            ),
        )
        current_source_bindings = current_resolved.source_bindings_config
        source_bindings_changed = (
            previous_source_bindings is not None
            and previous_source_bindings != current_source_bindings
        )
        self._pipeline_config = pipeline_config

        if source_bindings_changed:
            self._invalidate_source_projection()

        # CRITICAL FIX: Do NOT contaminate thread-local context during PipelineConfig editing
        # The orchestrator should maintain its own internal context without modifying
        # the global thread-local context. This prevents reset operations from showing
        # orchestrator's saved values instead of original thread-local defaults.
        #
        # The merged config is computed internally and used by get_effective_config()
        # but should NOT be set as the global thread-local context.

        logger.info(f"Applied orchestrator config for plate: {self.plate_path}")

    def _invalidate_source_projection(self) -> None:
        """Require normal initialization to rebuild source-owned plate state."""

        if (
            self.microscope_handler is not None
            and type(self.microscope_handler).projects_declared_source_bindings()
        ):
            self._microscope_handler_rebuild_type = type(self.microscope_handler)
        self.microscope_handler = None
        self.input_dir = None
        self._initialized = False
        self._state = OrchestratorState.CREATED
        self._component_keys_cache.clear()
        self.metadata_cache.clear_cache()

    def get_effective_config(
        self, *, for_serialization: bool = False
    ) -> GlobalPipelineConfig:
        """
        Get effective configuration for this orchestrator.

        Args:
            for_serialization: Retained for compatibility; the returned config is
                always the saved ObjectState-resolved concrete configuration.
        """

        if self.pipeline_config is None:
            raise RuntimeError("No pipeline configuration available for resolution")

        result, _ = ObjectState.resolve_saved_object(
            self.pipeline_config,
            ancestor_objects_with_scopes=(
                ObjectStateRegistry.get_ancestor_objects_with_scopes(
                    None, use_saved=True
                )
            ),
        )
        if not isinstance(result, GlobalPipelineConfig):
            raise TypeError(
                "Resolved pipeline configuration must be GlobalPipelineConfig, "
                f"got {type(result).__name__}."
            )
        return result

    def clear_pipeline_config(self) -> None:
        """Clear per-orchestrator configuration."""
        self.pipeline_config = None
        # Clear metadata cache for this orchestrator
        self.metadata_cache.clear_cache()
        logger.info(f"Cleared per-orchestrator config for plate: {self.plate_path}")

    def cleanup_pipeline_config(self) -> None:
        """Clean up orchestrator context when done (for backward compatibility)."""
        self.clear_pipeline_config()
