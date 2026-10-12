"""OpenHCS execution server built on zmqruntime ExecutionServer."""

from __future__ import annotations

import logging
import sys
import time
from collections.abc import Sequence
from dataclasses import dataclass, replace
from types import ModuleType

from polystore import cleanup_backend_connections
from polystore.base import ensure_storage_registry
from zmqruntime.config import TransportMode
from zmqruntime.execution import ExecutionServer
from zmqruntime.messages import (
    ExecuteRequest,
    ExecutionRecord,
    ExecutionStatus,
    StatusRequest,
)
from zmqruntime.startup import EndpointStartupStatusCallback

from openhcs.core.compiled_execution import CompiledExecutionBundle
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from objectstate.object_state import ObjectState
from objectstate.object_state_registry import ObjectStateRegistry
from openhcs.core.config_document import ConfigDocumentCodec
from openhcs.core.dataset_sources.discovery import discover_domain_registries
from openhcs.core.orchestrator.cancellation import ExecutionCancelledError
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.progress import ProgressEvent, ProgressExecutionContext
from openhcs.core.runtime_execution_validation import runtime_output_roots
from openhcs.core.steps.function_step import FunctionStep
from openhcs.runtime.environment_provenance import RuntimeEnvironmentSnapshot
from openhcs.runtime.import_authority import ImportRootEndpoint
from openhcs.runtime.kept_workers import KeptWorkers
from openhcs.runtime.zmq_application import OPENHCS_ENDPOINT_APPLICATION
from openhcs.runtime.zmq_compilation import (
    ZMQCompilationRequest,
    ZMQCompileArtifactRecord,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG, OpenHCSZMQConfig
from openhcs.runtime.zmq_control import (
    ZMQControlMessageRouter,
    ZMQControlRequestContext,
)
from openhcs.runtime.zmq_execution_signature import (
    OpenHCSExecutionConfigBundle,
    ZMQAuxiliaryExecutionParams,
    ZMQAuxiliaryParamField,
    ZMQExecutionRequestPayload,
)
from openhcs.runtime.zmq_orchestrator_environment import (
    ZMQOrchestratorEnvironmentRequest,
)
from openhcs.runtime.zmq_progress import ZMQCompilerProgressQueue, ZMQProgressEmitter
from openhcs.runtime.zmq_server_hooks import (
    ZMQResultsSummaryEnricher,
    ZMQWorkerCleanup,
)
from openhcs.runtime.zmq_worker_execution import ZMQWorkerExecutionRequest

logger = logging.getLogger(__name__)


@dataclass(frozen=True, slots=True)
class ZMQExecutionContext:
    """Request context shared by compile and execution completion phases."""

    execution_id: str
    request_payload: ZMQExecutionRequestPayload
    pipeline_steps: list[FunctionStep]
    configs: OpenHCSExecutionConfigBundle

    @property
    def pipeline_config(self) -> PipelineConfig:
        return self.configs.pipeline

    @property
    def subject_id(self) -> str:
        return self.request_payload.subject_id

    @property
    def execution_subject_id(self) -> str | None:
        return self.request_payload.execution_subject_id

    @property
    def config_params(self) -> dict | None:
        return self.request_payload.config_params

    @property
    def auxiliary_params(self) -> ZMQAuxiliaryExecutionParams:
        return ZMQAuxiliaryExecutionParams.from_transport(
            self.request_payload.config_params
        )

    @property
    def compile_only(self) -> bool:
        return self.request_payload.compile_only

    @property
    def compile_artifact_id(self) -> str | None:
        return self.request_payload.compile_artifact_id

    @property
    def request_signature(self) -> str:
        return self.request_payload.request_signature

    @property
    def compilation_signature(self) -> str:
        return self.request_payload.compilation_signature

    @property
    def debug_replay_signature(self) -> str:
        return self.request_payload.debug_replay_signature

    @property
    def pipeline_sha(self) -> str:
        return self.request_payload.pipeline_sha

    def validate_compile_request(self) -> None:
        if self.compile_only and self.compile_artifact_id:
            raise ValueError("compile_only and compile_artifact_id cannot both be set")

    def progress_context(self) -> ProgressExecutionContext:
        return ProgressExecutionContext(
            execution_id=self.execution_id, subject_id=self.subject_id
        )


class FunctionCatalogExecutionServer(ExecutionServer):
    """Own catalogue preparation across physical endpoint start and stop."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        from openhcs.agent.services.function_catalog_service import (
            FunctionCatalogService,
        )
        from openhcs.runtime.function_catalog_preparation import (
            FunctionCatalogPreparation,
        )

        self._function_catalog = FunctionCatalogService()
        self._function_catalog_preparation = FunctionCatalogPreparation(
            self._function_catalog
        )

    def prepare_runtime_capabilities(
        self,
        status_callback: EndpointStartupStatusCallback | None = None,
    ) -> None:
        """Prepare the catalog and what a first request would otherwise run once.

        The storage backend registry and the family registries that domains
        extend are completed by their owners here, so workers forked after
        this inherit them and no request pays for them.
        """
        self._function_catalog_preparation.prepare_before_serving(status_callback)
        ensure_storage_registry()
        discover_domain_registries()

    def start(self) -> None:
        self.prepare_runtime_capabilities()
        super().start()

    def stop(self) -> None:
        try:
            super().stop()
        finally:
            self._function_catalog_preparation.cancel_and_join()


class ZMQExecutionServer(ImportRootEndpoint, FunctionCatalogExecutionServer):
    """OpenHCS-specific execution server."""

    _server_type = "execution"

    def __init__(
        self,
        port: int | None = None,
        host: str | None = None,
        log_file_path: str | None = None,
        transport_mode: TransportMode | None = None,
        config: OpenHCSZMQConfig = OPENHCS_ZMQ_CONFIG,
    ):
        super().__init__(
            port=config.default_port if port is None else port,
            host=config.server_host if host is None else host,
            log_file_path=log_file_path,
            transport_mode=(
                config.transport_mode if transport_mode is None else transport_mode
            ),
            config=config,
            application=OPENHCS_ENDPOINT_APPLICATION,
        )
        self._compile_status: str | None = None
        self._compile_message: str | None = None
        self._compile_status_expires_at: float | None = None
        self._worker_assignments_by_execution: dict[str, dict[str, list[str]]] = {}
        self._compiled_artifacts: dict[str, ZMQCompileArtifactRecord] = {}
        self._compiled_artifact_ttl_seconds = config.compiled_artifact_ttl_seconds
        self._server_environment = RuntimeEnvironmentSnapshot.current()
        self._workers = KeptWorkers()

    def prepare_runtime_capabilities(
        self,
        status_callback: EndpointStartupStatusCallback | None = None,
    ) -> None:
        super().prepare_runtime_capabilities(status_callback)
        self._workers.start_inheriting_workers()

    def stop(self) -> None:
        """Stop transport and every exact process resource owned by this server."""

        self._running = False
        try:
            try:
                ZMQWorkerCleanup(self.active_executions).cancel_orchestrators()
            finally:
                self._workers.close()
        finally:
            try:
                super().stop()
            finally:
                cleanup_backend_connections(include_process_resources=True)

    def handle_control_message(self, message):
        if ZMQControlMessageRouter.handles(message):
            self._cleanup_compiled_artifacts()
            return ZMQControlMessageRouter.handle(
                message,
                ZMQControlRequestContext(
                    compiled_artifacts=self._compiled_artifacts,
                    function_catalog=self._function_catalog,
                    function_catalog_preparation=self._function_catalog_preparation,
                ),
            )
        return super().handle_control_message(message)

    def _set_compile_status(
        self, status: str, message: str | None = None, ttl_seconds: float = 4.0
    ) -> None:
        self._compile_status = status
        self._compile_message = message
        self._compile_status_expires_at = time.time() + ttl_seconds

    def _get_compile_status(self) -> tuple[str | None, str | None]:
        if self._compile_status_expires_at is None:
            return None, None
        if time.time() > self._compile_status_expires_at:
            self._compile_status = None
            self._compile_message = None
            self._compile_status_expires_at = None
            return None, None
        return self._compile_status, self._compile_message

    def _cleanup_compiled_artifacts(self) -> None:
        now = time.time()
        expired_ids = [
            artifact_id
            for artifact_id, artifact in self._compiled_artifacts.items()
            if now - artifact.created_at > self._compiled_artifact_ttl_seconds
        ]
        for artifact_id in expired_ids:
            del self._compiled_artifacts[artifact_id]
        if expired_ids:
            logger.info("Cleaned up %d expired compile artifact(s)", len(expired_ids))

    def _create_pong_response(self):
        self._cleanup_compiled_artifacts()
        compile_status, compile_message = self._get_compile_status()
        return replace(
            super()._create_pong_response(),
            compile_status=compile_status,
            compile_message=compile_message,
        )

    def _enqueue_progress(self, event: ProgressEvent) -> None:
        self.send_progress_update(event.to_dict())

    def _forward_worker_progress(self, worker_queue) -> None:
        """Publish worker progress with the execution's lane topology attached."""

        while (event := worker_queue.get()) is not None:
            assignments = self._worker_assignments_for_execution(event.execution_id)
            # Axisless events are owned by the parent execution lifecycle, not
            # by a worker lane. They carry topology but never a worker claim.
            if event.axis_id:
                self._require_worker_claim(event, assignments)
            elif event.worker_slot is not None or event.owned_partition_values is not None:
                raise ValueError(
                    f"Execution-level progress cannot carry a worker claim: {event}"
                )
            self._enqueue_progress(
                event.with_worker_topology(
                    worker_assignments=assignments,
                    partition_values=sorted(
                        axis_id
                        for assigned_axes in assignments.values()
                        for axis_id in assigned_axes
                    ),
                )
            )

    @staticmethod
    def _require_worker_claim(
        event: ProgressEvent,
        assignments: dict[str, list[str]],
    ) -> None:
        """A lane event must name a planned lane and exactly that lane's values."""

        if event.worker_slot not in assignments:
            raise ValueError(
                f"Unknown worker_slot {event.worker_slot!r}. "
                f"Expected one of: {list(assignments)}"
            )
        expected = assignments[event.worker_slot]
        if sorted(event.owned_partition_values or ()) != sorted(expected):
            raise ValueError(
                f"Invalid worker claim for {event.worker_slot}: expected={expected}, "
                f"got={event.owned_partition_values}"
            )

    def _worker_assignments_for_execution(
        self,
        execution_id: str,
    ) -> dict[str, list[str]]:
        if execution_id not in self._worker_assignments_by_execution:
            raise ValueError(
                f"Missing worker assignments for execution_id={execution_id}"
            )
        return self._worker_assignments_by_execution[execution_id]

    def _get_worker_info(self):
        """Return raw worker info (no enrichment).

        Worker axis_id comes from progress tracker, not from ping responses.
        Ping is for process tracking (CPU, memory), not application state.
        """
        return super()._get_worker_info()

    def _attach_results_summary_extras(
        self, execution_id: str, record, execution_payload: dict | None = None
    ) -> None:
        ZMQResultsSummaryEnricher(self.active_executions).attach(
            execution_id=execution_id,
            record=record,
            execution_payload=execution_payload,
        )

    def finalize_execution_record(self, record: ExecutionRecord) -> None:
        """Attach OpenHCS summary fields before terminal status is published."""
        try:
            self._attach_results_summary_extras(
                execution_id=record.execution_id, record=record
            )
        except Exception as e:
            logger.warning(
                "[%s] Failed to attach output_dataset_root to results_summary: %s",
                record.execution_id,
                e,
            )

    def handle_status(self, msg):
        response = super().handle_status(msg)
        return ZMQResultsSummaryEnricher(
            self.active_executions
        ).attach_to_status_response(
            execution_id=StatusRequest.from_dict(msg).execution_id,
            response=response,
        )

    def execute_task(self, execution_id: str, request: ExecuteRequest):
        return self._execute_pipeline(
            execution_id,
            ZMQExecutionRequestPayload.from_execute_request(request),
        )

    def _execute_pipeline(
        self,
        execution_id: str,
        request_payload: ZMQExecutionRequestPayload,
    ):
        logger.info("[%s] Starting subject %s", execution_id, request_payload.subject_id)

        request_payload.compile_control.validate()
        self._cleanup_compiled_artifacts()
        if request_payload.compile_artifact_id is not None:
            artifact = self._compiled_artifacts.get(request_payload.compile_artifact_id)
            if artifact is None:
                raise ValueError(
                    f"Missing compile artifact '{request_payload.compile_artifact_id}'. "
                    "Re-run compilation before execution."
                )
            auxiliary = ZMQAuxiliaryExecutionParams.from_transport(
                request_payload.config_params
            )
            retain = self._retain_compile_artifact(auxiliary.debug_execution_config)
            artifact.require_compatible_request(
                subject_id=request_payload.subject_id,
                signature=(
                    request_payload.debug_replay_signature
                    if retain
                    else request_payload.compilation_signature
                ),
                retain_compile_artifact=retain,
            )
            return self._execute_with_orchestrator(
                ZMQExecutionContext(
                    execution_id=execution_id,
                    request_payload=request_payload,
                    pipeline_steps=list(
                        artifact.compilation.execution_bundle.pipeline_definition
                    ),
                    configs=artifact.configs,
                )
            )

        import openhcs.processing.func_registry as func_registry_module

        if func_registry_module.pipeline_source_requires_import_projection(
            request_payload.pipeline_code
        ):
            func_registry_module.initialize_registry()

        module_name = f"openhcs_zmq_pipeline_{request_payload.pipeline_sha}"
        module = ModuleType(module_name)
        module.__file__ = f"<{module_name}>"
        sys.modules[module_name] = module
        try:
            exec(
                compile(
                    request_payload.pipeline_code,
                    module.__file__,
                    "exec",
                ),
                module.__dict__,
            )
        finally:
            sys.modules.pop(module_name, None)
        pipeline_document = PipelineDocumentCodec.from_namespace(module.__dict__)
        resolved_config = self._resolve_request_config(
            request_payload,
            pipeline_document.pipeline_config,
        )
        request_context = ZMQExecutionContext(
            execution_id=execution_id,
            request_payload=request_payload,
            pipeline_steps=pipeline_document.pipeline_steps,
            configs=resolved_config,
        )
        request_context.validate_compile_request()
        logger.info(
            "[%s] Request received: subject=%s compile_only=%s artifact_id=%s step_count=%d pipeline_sha=%s request_sig=%s",
            execution_id,
            request_context.subject_id,
            request_context.compile_only,
            request_context.compile_artifact_id,
            len(request_context.pipeline_steps),
            request_context.pipeline_sha,
            request_context.request_signature[:12],
        )

        try:
            return self._execute_with_orchestrator(request_context)
        except ExecutionCancelledError:
            raise
        except Exception as e:
            if request_payload.compile_only:
                self._set_compile_status("compile failed", str(e))
            raise

    def _resolve_request_config(
        self,
        request_payload: ZMQExecutionRequestPayload,
        pipeline_config: PipelineConfig,
    ) -> OpenHCSExecutionConfigBundle:
        if request_payload.config_code is not None:
            global_config = ConfigDocumentCodec.from_source(
                request_payload.config_code,
                expected_config_type=GlobalPipelineConfig,
            )
            return OpenHCSExecutionConfigBundle(
                global_pipeline=global_config,
                pipeline=pipeline_config,
            )
        raise ValueError("config_code is required for execution config resolution")

    def _execute_with_orchestrator(
        self,
        request_context: ZMQExecutionContext,
    ):
        from openhcs.core.debug import DebugPausedWorkerRegistry

        auxiliary_params = request_context.auxiliary_params
        environment = ZMQOrchestratorEnvironmentRequest(
            execution_id=request_context.execution_id,
            subject_id=request_context.subject_id,
            execution_subject_id=request_context.execution_subject_id,
            selected_pipeline_path=request_context.request_payload.selected_pipeline_path,
            debug_execution_config=auxiliary_params.debug_execution_config,
        ).prepare()
        debug_execution_policy = environment.debug_execution_policy
        debug_execution_config = environment.debug_execution_config
        dataset_root = environment.dataset_root

        progress_context = request_context.progress_context()
        progress_emitter = ZMQProgressEmitter(
            enqueue=self._enqueue_progress,
            execution_id=request_context.execution_id,
            subject_id=request_context.subject_id,
        )

        partition_values: list[str] | None = None
        compilation_resolved = False
        try:
            self._emit_compile_started(
                progress_emitter,
                request_context.pipeline_steps,
                request_context.compile_artifact_id,
            )
            self._ensure_request_global_config_context(request_context)
            execution_bundle = (
                self._compiled_artifacts[
                    request_context.compile_artifact_id
                ].compilation.execution_bundle
                if request_context.compile_artifact_id is not None
                else None
            )
            resolved_config = None
            if execution_bundle is None:
                resolved_config, _ = ObjectState.resolve_saved_object(
                    request_context.pipeline_config,
                    ancestor_objects_with_scopes=(
                        ObjectStateRegistry.get_ancestor_objects_with_scopes(
                            None, use_saved=True
                        )
                    ),
                )
            orchestrator = self._initialize_orchestrator(
                request_context.execution_id,
                dataset_root,
                request_context.pipeline_config,
                resolved_config=resolved_config,
                selected_pipeline_path=request_context.request_payload.selected_pipeline_path,
                execution_bundle=execution_bundle,
            )
            self._raise_if_cancelled(request_context.execution_id, "initialization")
            partition_values = self._partition_values_for_execution(
                auxiliary_params.partition_values,
                orchestrator,
                debug_execution_policy,
                execution_bundle=execution_bundle,
            )
            self._emit_planned_init_started(
                progress_emitter,
                request_context.pipeline_steps,
                partition_values,
                request_context.compile_artifact_id,
            )
            compilation = self._resolve_compilation(
                request_context=request_context,
                orchestrator=orchestrator,
                partition_values=partition_values,
                debug_execution_config=debug_execution_config,
                debug_execution_policy=debug_execution_policy,
                progress_emitter=progress_emitter,
                resolved_config=resolved_config,
            )
            compilation_resolved = True
            self._record_compilation_outputs(request_context.execution_id, compilation)
            self._raise_if_cancelled(request_context.execution_id, "compilation")
            return self._finish_compilation_or_execute(
                request_context=request_context,
                orchestrator=orchestrator,
                compilation=compilation,
                progress_context=progress_context,
                debug_execution_policy=debug_execution_policy,
            )
        except ExecutionCancelledError:
            raise
        except Exception as error:
            self._emit_compile_failure(
                progress_emitter=progress_emitter,
                compile_artifact_id=request_context.compile_artifact_id,
                compilation_resolved=compilation_resolved,
                partition_values=partition_values,
                error=error,
            )
            raise
        finally:
            if (
                debug_execution_config is not None
                and debug_execution_config.replay_mode.keeps_worker_paused
            ):
                DebugPausedWorkerRegistry.remove(
                    debug_execution_config.debug_session_id
                )
            self._worker_assignments_by_execution.pop(
                request_context.execution_id,
                None,
            )

    @staticmethod
    def _emit_compile_started(
        progress_emitter: ZMQProgressEmitter,
        pipeline_steps: Sequence[FunctionStep],
        compile_artifact_id: str | None,
    ) -> None:
        if compile_artifact_id is None:
            progress_emitter.compile_started(len(pipeline_steps))

    def _initialize_orchestrator(
        self,
        execution_id: str,
        dataset_root: str,
        pipeline_config,
        *,
        resolved_config: GlobalPipelineConfig | None,
        selected_pipeline_path: str | None = None,
        execution_bundle: CompiledExecutionBundle | None = None,
    ):
        from pathlib import Path

        from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator

        if execution_bundle is None:
            if resolved_config is None:
                raise ValueError("Fresh initialization requires resolved configuration.")
            orchestrator = PipelineOrchestrator(
                dataset_root=Path(dataset_root),
                pipeline_config=pipeline_config,
                resolved_config=resolved_config,
                selected_pipeline_path=selected_pipeline_path,
                progress_callback=None,
                transport_config=self.config,
            )
            orchestrator.execution_id = execution_id
            orchestrator.initialize(resolved_config=resolved_config)
        else:
            orchestrator = PipelineOrchestrator.from_compiled_execution(
                execution_bundle,
                dataset_root=Path(dataset_root),
                pipeline_config=pipeline_config,
                selected_pipeline_path=selected_pipeline_path,
                transport_config=self.config,
            )
        orchestrator.execution_id = execution_id
        self.active_executions[execution_id].set_extra("orchestrator", orchestrator)
        return orchestrator

    def _raise_if_cancelled(self, execution_id: str, phase_name: str) -> None:
        if (
            self.active_executions[execution_id].status
            == ExecutionStatus.CANCELLED.value
        ):
            logger.info(
                "[%s] Execution cancelled after %s, aborting",
                execution_id,
                phase_name,
            )
            raise ExecutionCancelledError("Execution cancelled by user")

    @staticmethod
    def _partition_values_for_execution(
        axis_filter: tuple[str, ...] | None,
        orchestrator,
        debug_execution_policy,
        *,
        execution_bundle: CompiledExecutionBundle | None = None,
    ) -> list[str]:
        from openhcs.core.axes import AxisFamily

        if axis_filter is not None:
            return list(axis_filter)
        available_axis_ids = (
            execution_bundle.axis_ids
            if execution_bundle is not None
            else tuple(
                orchestrator.get_component_keys(
                    AxisFamily.active().partition_axis()
                )
            )
        )
        return debug_execution_policy.axis_filter_for_available(available_axis_ids)

    @staticmethod
    def _emit_planned_init_started(
        progress_emitter: ZMQProgressEmitter,
        pipeline_steps: Sequence[FunctionStep],
        partition_values: list[str],
        compile_artifact_id: str | None,
    ) -> None:
        if compile_artifact_id is None:
            progress_emitter.planned_init_started(
                partition_values=partition_values,
                step_names=[step.name for step in pipeline_steps],
            )

    def _resolve_compilation(
        self,
        *,
        request_context: ZMQExecutionContext,
        orchestrator,
        partition_values: list[str],
        debug_execution_config,
        debug_execution_policy,
        progress_emitter: ZMQProgressEmitter,
        resolved_config: GlobalPipelineConfig | None,
    ):
        if request_context.compile_artifact_id is not None:
            self._cleanup_compiled_artifacts()
        return ZMQCompilationRequest(
            execution_id=request_context.execution_id,
            subject_id=request_context.subject_id,
            pipeline_steps=request_context.pipeline_steps,
            orchestrator=orchestrator,
            resolved_config=resolved_config,
            partition_values=partition_values,
            compile_artifact_id=request_context.compile_artifact_id,
            compilation_signature=request_context.compilation_signature,
            debug_replay_signature=request_context.debug_replay_signature,
            retain_compile_artifact=self._retain_compile_artifact(
                debug_execution_config
            ),
            compiled_artifacts=self._compiled_artifacts,
            progress_emitter=progress_emitter,
            compiler_progress_queue=ZMQCompilerProgressQueue(
                enqueue=self._enqueue_progress,
                subject_id=request_context.subject_id,
            ),
            debug_execution_policy=debug_execution_policy,
            consumes_artifact=not request_context.auxiliary_params.prepare_workers_only,
        ).resolve()

    @staticmethod
    def _retain_compile_artifact(debug_execution_config) -> bool:
        if debug_execution_config is None:
            return False
        return debug_execution_config.replay_mode.retains_compile_artifact

    def _record_compilation_outputs(self, execution_id: str, compilation) -> None:
        self._worker_assignments_by_execution[execution_id] = (
            compilation.worker_assignments
        )
        if compilation.output_dataset.is_present:
            self.active_executions[execution_id].set_extra(
                compilation.output_dataset.EXECUTION_RECORD_KEY,
                compilation.output_dataset,
            )

    def _finish_compilation_or_execute(
        self,
        *,
        request_context: ZMQExecutionContext,
        orchestrator,
        compilation,
        progress_context: ProgressExecutionContext,
        debug_execution_policy,
    ):
        if request_context.compile_only:
            return self._store_compile_artifact(
                request_context=request_context,
                compilation=compilation,
            )
        if request_context.auxiliary_params.prepare_workers_only:
            return self._workers.prepare_pipeline(
                request_context.execution_id, compilation.execution_bundle
            )
        execution_results = ZMQWorkerExecutionRequest(
            execution_id=request_context.execution_id,
            orchestrator=orchestrator,
            execution_bundle=compilation.execution_bundle,
            runtime_observation_mode=(
                request_context.auxiliary_params.runtime_observation_mode_for(
                    compilation.execution_bundle
                )
            ),
            progress_context=progress_context,
            debug_execution_policy=debug_execution_policy,
            active_execution_record=self.active_executions[
                request_context.execution_id
            ],
            forward_worker_progress=self._forward_worker_progress,
            workers=self._workers,
        ).execute()
        self._export_runtime_observation(
            request_context=request_context,
            compilation=compilation,
            execution_results=execution_results,
        )
        execution_results.require_success()
        return execution_results

    def _export_runtime_observation(
        self,
        *,
        request_context: ZMQExecutionContext,
        compilation,
        execution_results,
    ) -> None:
        export_path = request_context.auxiliary_params.runtime_observation_export_path
        if export_path is None:
            return

        execution_bundle = compilation.execution_bundle
        output_roots = runtime_output_roots(
            execution_bundle.runtime_contexts,
            compilation.output_dataset.output_dataset_root,
        )
        export = request_context.auxiliary_params.runtime_observation_export_scope.export(
            execution_bundle=execution_bundle,
            execution_results=execution_results,
            output_roots=output_roots,
            server_environment=self._server_environment,
            execution_id=request_context.execution_id,
        )
        export.write(export_path)
        self.active_executions[request_context.execution_id].set_extra(
            ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_PATH.value,
            str(export_path),
        )
        self.active_executions[request_context.execution_id].set_extra(
            ZMQAuxiliaryParamField.RUNTIME_OBSERVATION_EXPORT_SCOPE.value,
            request_context.auxiliary_params.runtime_observation_export_scope.name,
        )
        logger.info(
            "[%s] Exported runtime observation to %s",
            request_context.execution_id,
            export_path,
        )

    def _store_compile_artifact(
        self,
        *,
        request_context: ZMQExecutionContext,
        compilation,
    ):
        self._compiled_artifacts[request_context.execution_id] = (
            ZMQCompileArtifactRecord(
                execution_id=request_context.execution_id,
                subject_id=request_context.subject_id,
                compilation_signature=request_context.compilation_signature,
                debug_replay_signature=request_context.debug_replay_signature,
                compilation=compilation,
                configs=request_context.configs,
            )
        )
        logger.info(
            "[%s] Compilation-only request completed and artifact stored (artifact_id=%s sig=%s)",
            request_context.execution_id,
            request_context.execution_id,
            request_context.compilation_signature[:12],
        )
        self._set_compile_status("compiled success")
        return compilation.execution_bundle.runtime_contexts

    def _emit_compile_failure(
        self,
        *,
        progress_emitter: ZMQProgressEmitter,
        compile_artifact_id: str | None,
        compilation_resolved: bool,
        partition_values: list[str] | None,
        error: Exception,
    ) -> None:
        if compile_artifact_id is not None:
            return
        if compilation_resolved:
            return
        progress_emitter.compile_failed(
            axis_ids=self._compile_failure_axis_ids(partition_values),
            error=str(error),
        )

    @staticmethod
    def _ensure_request_global_config_context(
        request_context: ZMQExecutionContext,
    ) -> None:
        from objectstate.lazy_factory import (
            ensure_global_config_context,
        )

        ensure_global_config_context(
            GlobalPipelineConfig,
            request_context.configs.global_pipeline,
        )

    @staticmethod
    def _compile_failure_axis_ids(partition_values: list[str] | None) -> list[str]:
        if partition_values is None:
            return []
        return partition_values

    def _kill_worker_processes(self) -> int:
        """OpenHCS-specific worker cleanup (graceful cancellation + kill)."""
        return ZMQWorkerCleanup(self.active_executions).cancel_orchestrators()

    def _interrupt_execution(self, execution_id: str) -> int:
        """Cancel the targeted orchestrator before terminating its workers."""

        return ZMQWorkerCleanup(self.active_executions).cancel_execution(execution_id)
